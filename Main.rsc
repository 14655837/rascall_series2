module Main

import util::IDEServices;
import lang::java::m3::Core;
import lang::java::m3::AST;

import IO;
import List;
import Set;
import String;
import Map;
import Node;

// Definitions:

// Definition Type I: exact copy, ignoring whitespace and comments.
// int x ▷◁ int x and int x ̸ ▷◁ int y
// Definition Type II: syntactical copy, changes allowed in variable, type, function identifiers.
// int x ▷◁ int y
// Definition Type III: copy with changed, added, and deleted statements.
// print(a); print(c) ▷◁ print(a); print(b); print(c)
// Definition Type IV: functionality is the same, code may be completely different.
// a && b ▷◁ a ? b : false

// Ast creator
list[Declaration] getASTs(loc projectLocation) {
    M3 model = createM3FromMavenProject(projectLocation);
    list[Declaration] asts = [createAstFromFile(f, true)
        | f <- files(model.containment), isCompilationUnit(f)];
    return asts;
}

// Task 1

// An AST-based clone detector whose back-end is written in Rascal that
// detects at least Type I clones in a Java project:
// • Detected clone classes are written to a file in a textual representation.
// • Clone classes that are strictly included in others are dropped from
// the results (subsumption)

// Algoritm:
// 1. Clones=∅
// 2. For each subtree i:
// If mass(i)>=MassThreshold
// Then hash i to bucket
// 3. For each subtree i and j in the same bucket
// If CompareTree(i,j) > SimilarityThreshold
// Then { For each subtree s of i
//  If IsMember(Clones,s)
//  Then RemoveClonePair(Clones,s)
// For each subtree s of j
//  If IsMember(Clones,s)
//  Then RemoveClonePair(Clones,s)
// AddClonePair(Clones,i,j)
//  }

// Similarity = 2 x S / (2 x S + L + R)
// Where,
// S = number of shared nodes
// L = number of different nodes in sub-tree 1
// R = number of different nodes in sub-tree 2

// TODO rewrite this function!
// NOT USED NOW!!
public lrel[node,node] removeSymmetricPairs(lrel[node,node] clone_pairs) {
    lrel[node,node] new_clone_pairs = [];
    for (pair <- clone_pairs) {
        tuple[node, node] reverse_pair = <pair[1], pair[0]>;
        if (reverse_pair notin new_clone_pairs) {
            new_clone_pairs += pair;
        }
    }
    return new_clone_pairs;
}

num similarity(node ast1, node ast2) {
    list[node] nodes_ast1 = [];
    list[node] nodes_ast2 = [];

    // find all nodes in the two asts
    visit(ast1) {
        case node n: {nodes_ast1 += n;}
    }
    visit(ast2) {
        case node n: {nodes_ast2 += n;}
    }

    // compare the two nodes
    list[node] overlap = nodes_ast1 & nodes_ast2;
    list[node] only_ast1 = nodes_ast1 - nodes_ast2;
    list[node] only_ast2 = nodes_ast2 - nodes_ast1;

    num S = size(overlap);
    num R = size(only_ast1);
    num L = size(only_ast2);

    num sim = 2.0 * S / (2.0 * S + R + L);

    return sim;
}

int calc_mass(node a_node) {
    int counter = 0;

    visit(a_node) {
        case node n: {counter += 1;}
    }

    return counter;
}

node strip_location(node n) {
    // Recursively remove the `src` keyword parameter from the key node
    // (We keep the original node with src separate in `original`)
    n = unsetRec(n);
    return n;
}

bool min_line_count(loc location, int lines) {
    int totalLines = location.end.line - location.begin.line;
	if (totalLines >= lines) {
        // println("Location <location> has <totalLines> lines.");
		return true;
	}
	return false;
}

// helper: true if inner is strictly inside outer (same file, smaller range)
bool is_inside(loc inner, loc outer) {
    return inner.scheme == outer.scheme
        && inner.authority == outer.authority
        && inner.path == outer.path
        && outer.offset <= inner.offset
        && outer.offset + outer.length >= inner.offset + inner.length
        && (inner.offset != outer.offset || inner.length != outer.length);
}

// "Similar" to your Java approach: treat every clone node as a candidate
// and drop those that live *inside* another clone.
list[list[node]] remove_child_clones_per_class(list[list[node]] clone_classes) {
    list[list[node]] result = [];

    for (cls <- clone_classes) {
        set[node] to_remove = {};

        for (n <- cls) {
            // check if n is inside some *other* node in the same clone classes
            for (other_cls <- clone_classes) {
                for (m <- other_cls) {
                    if (n == m || !(m has src)) {
                        continue;
                    }
                    if (is_inside(n.src, m.src)) {
                        to_remove += { n };
                        break;
                    }
                }
                if (n in to_remove) {
                    break;
                }
            }
        }

        list[node] filtered = [ n | n <- cls, !(n in to_remove) ];
        if (size(filtered) >= 2) {
            result += [ filtered ];
        }
    }

    return result;
}

list[list[node]] find_clones_type1(list[Declaration] asts, int treshold) {
    // Step 1: bucket by mass, like in your original version
    map[int, list[node]] bucket = ();
    visit(asts) {
        case node n: {
            int mass = calc_mass(n);
            // puts the node in a bucket
            if (mass >= treshold) {
                if (mass in bucket) {
                    list[node] current_item = bucket[mass];
                    bucket[mass] = current_item + [n];
                } else {
                    bucket[mass] = [n];
                }
            }
        }
    }

    list[list[node]] all_clones = [];
    int done_buckets = 0;
    int total_buckets = size(bucket);

    // Step 2: for each mass-bucket, group by exact subtree
    for (b <- bucket) {
        done_buckets += 1;
        if (done_buckets % 50 == 0) {
            println("Processed <done_buckets>/<total_buckets> buckets...");
        }

        int bucketSize = size(bucket[b]);
        if (bucketSize >= 2) {

            // group by exact subtree value inside the mass bucket
            map[node, list[node]] exact_buckets = ();
            for (n_old <- bucket[b]) {
                if (!(n_old has src)) {
                    continue;
                }
                if (!min_line_count(n_old.src, 6)) {
                    continue;
                }
                node n = strip_location(n_old);
                // println("n: <n>\n\n\n");
                // println("Processing node with src: <n_old.src>");
                if (exact_buckets[n]?) {
                    exact_buckets[n] += [n_old];
                } else {
                    exact_buckets[n] = [n_old];
                }
                
            }            

            // Each exactBucket with size >= 2 is a Type I clone class
            for (k <- exact_buckets) {
                if (size(exact_buckets[k]) >= 2) {
                    // optionally show some structure
                    all_clones += [exact_buckets[k]];
                }
            }
        }
    }

    all_clones = remove_child_clones_per_class(all_clones);

    return all_clones;
}

int compute_LOC(loc location){
	int count = 0;
	str content = readFile(location);
	comment_free = visit(content){
		case /(\/\*[\s\S]*?\*\/|\/\/[\s\S]*?(\n|\r))/ => ""
	}
	list[str] lines = split("\n", comment_free);
	for( i <- lines, trim(i) != "")
		count += 1;
	return count;
}

void write_and_print_report(list[list[node]] clone_classes, loc project_location, loc json_output_location) {

    // calculate % of duplicate lines and biggest clone

    num total_lines = 0;
    num duplicate_lines = 0;
    num biggest_clone_in_lines = 0;

    M3 model = createM3FromMavenProject(project_location);

    // map lines per file
    map[loc, int] lines_per_file = ();

    for (f <- files(model.containment), isCompilationUnit(f)) {
        int lines_in_file = compute_LOC(f);
        total_lines += lines_in_file;
        lines_per_file[f] = lines_in_file;
    }

    for (clones <- clone_classes) {
        num class_size = size(clones);
        num loc_per_clone = compute_LOC(clones[0].src);
        if (loc_per_clone > biggest_clone_in_lines) {
            biggest_clone_in_lines = loc_per_clone;
            node biggest_clone = clones[0];
        }
        duplicate_lines += loc_per_clone * class_size;
    }

    num duplicate_percentage = (duplicate_lines / total_lines) * 100.0;

    // calculate number of clones
    num total_clones = 0;
    for (clones <- clone_classes) {
        total_clones += size(clones);
    }

    // calculate number of clone classes
    num total_clone_classes = size(clone_classes);


    // print and write report

    str output = "";

    output += "{";
    output += "\n  \"total_lines\": <total_lines>,";
    output += "\n  \"duplicate_lines\": <duplicate_lines>,";
    output += "\n  \"duplicate_percentage\": <duplicate_percentage>,";
    output += "\n  \"total_clones\": <total_clones>,";
    output += "\n  \"total_clone_classes\": <total_clone_classes>,";
    output += "\n  \"biggest_clone_in_lines\": <biggest_clone_in_lines>,";

    println("Total lines of code: <total_lines>");
    println("Total duplicate lines of code: <duplicate_lines> (<duplicate_percentage>% )");
    println("Total number of clones: <total_clones>");
    println("Total number of clone classes: <total_clone_classes>");
    println("Biggest clone class size in lines: <biggest_clone_in_lines>");

    println("=== Example clone classes ===");

    // start JSON field for example clone classes
    output += "\n  \"example_clone_classes\": {";

    int shown = 0;
    bool first_class = true;

    for (list[node] cls <- clone_classes) {
        shown += 1;

        // JSON ALWAYS gets written
        if (!first_class) {
            output += ",\n";
        } else {
            output += "\n";
            first_class = false;
        }

        // JSON: always output every clone class
        output += "    \"Clone_class<shown>\": [";

        bool first_clone = true;
        for (node c <- cls) {
            if (!first_clone) {
                output += ", ";
            } else {
                first_clone = false;
            }
            output += "\"<c.src>\"";
        }

        output += "]";

        // Console: ONLY print first 5 classes
        if (shown <= 5) {
            println("\nClone class <shown> (size = <size(cls)>):");
            for (node c <- cls) {
                println("  - <c.src>");
            }
        } else if (shown == 6) {
            println("\n... (remaining clone classes omitted from console output)");
        }
    }

    output += "\n  },";
    output += "\n  \"lines_per_file\": {";

    shown = 0;
    first_class = true;

    for (f <- lines_per_file) {
        shown += 1;

        if (!first_class) {
            output += ",\n";
        } else {
            output += "\n";
            first_class = false;
        }
        output += "    \"<f>\": <lines_per_file[f]>";

        if (shown <= 5) {
            println("\nFile <f> has <lines_per_file[f]> lines");
        } else if (shown == 6) {
            println("\n... (remaining file lengths omitted from console output)");
        }
    }


    // close exampleCloneClasses object and the top-level JSON object
    output += "\n  }\n";
    output += "}\n";
    writeFile(json_output_location, output);
}

int main(int testArgument=0) {
    // loc folder_name = |file:///C:/Users/colin/Downloads/smallsql0.21_src/smallsql0.21_src/|;
    // loc folder_name = |file:///C:/Users/colin/Downloads/hsqldb-2.3.1/hsqldb-2.3.1/|;
    // loc folder_name = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/test_files|;
    //loc folder_name = |file:///C:/Users/Mikev/Downloads/smallsql0.21_src/smallsql0.21_src|;
    loc folder_name = |file:///C:/Users/Mikev/Downloads/hsqldb-2.3.1/hsqldb-2.3.1|;
    
    //loc json_output_location = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/clone_report_type1.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/smallsq_clone_report_type1.json|;
    loc json_output_location = |file:///C:/SE_master/rascall_series2_working/hsqldb_clone_report_type1.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/smallsq_clone_report_type1_test.json|;

    list[Declaration] asts = getASTs(folder_name);
    list[list[node]] clones_type1 = find_clones_type1(asts, 5);

    write_and_print_report(clones_type1, folder_name, json_output_location);

    return testArgument;
}
