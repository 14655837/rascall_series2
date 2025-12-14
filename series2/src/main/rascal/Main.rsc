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
import Type;

// Ast creator
list[Declaration] getASTs(loc projectLocation) {
    M3 model = createM3FromMavenProject(projectLocation);
    list[Declaration] asts = [createAstFromFile(f, true)
        | f <- files(model.containment), isCompilationUnit(f)];
    return asts;
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
                if (exact_buckets[n]?) {
                    exact_buckets[n] += [n_old];
                } else {
                    exact_buckets[n] = [n_old];
                }
                
            }            

            // Each exactBucket with size >= 2 is a Type I clone class
            for (k <- exact_buckets) {
                if (size(exact_buckets[k]) >= 2) {
                    all_clones += [exact_buckets[k]];
                }
            }
        }
    }

    all_clones = remove_child_clones_per_class(all_clones);

    return all_clones;
}

node normalize_node_to_type2(node n) {
    return visit(n) {
        case \method(a,b,c,_,d,e,f) => \method(a,b,c,id("const_method_name"),d,e,f)
        case \method(a,b,c,_,d,e)   => \method(a,b,c,id("const_method_name"),d,e)
        case \constructor(a,_,b,c,d) => \constructor(a,id("const_ctor_name"),b,c,d)
        case \class(a,_,b,c,d,e) => \class(a,id("const_class_name"),b,c,d,e)
        case \interface(a,_,b,c,d,e) => \interface(a,id("const_interface_name"),b,c,d,e)
        case \enum(a,_,b,c,d) => \enum(a,id("const_enum_name"),b,c,d)
        case \enumConstant(a,_,b,c) => \enumConstant(a,id("const_enum_const"),b,c)
        case \enumConstant(a,_,b) => \enumConstant(a,id("const_enum_const"),b)
        case \variable(_,a) => \variable(id("const_var_name"),a)
        case \variable(_,a,b) => \variable(id("const_var_name"),a,b)
        case \parameter(a,b,_,c) => \parameter(a,b,id("const_par_name"),c)
        case \vararg(a,b,_) => \vararg(a,b,id("const_var_arg"))
        case \annotationType(a,_,b) => \annotationType(a,id("const_annotation_name"),b)
        case \annotationTypeMember(a,b,_) => \annotationTypeMember(a,b,id("const_ann_member"))
        case \annotationTypeMember(a,b,_,c) => \annotationTypeMember(a,b,id("const_ann_member"),c)
        case \import(a,_) => \import(a,id("const_import"))
        case \importOnDemand(a,_) => \importOnDemand(a,id("const_import"))
        case \package(a,_) => \package(a,id("const_package"))
        case \stringLiteral(_) => \stringLiteral("string_literal")
		case \characterLiteral(_) => \characterLiteral("l")
    }
}



// Type 2 is a syntactically identical copy; only variable, type, or function
// identifiers have been changed.
// Almost same as type 1, but when comparing changed to normalized version, and
//  there is an extra check for if they are not inside type 1 clones.

list[list[node]] find_clones_type2(list[Declaration] asts, int treshold) {
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
    list[node] all_clones_type1 = [];
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
            map[node, list[node]] exact_buckets_type1 = ();
            for (n_old <- bucket[b]) {
                if (!(n_old has src)) {
                    continue;
                }
                if (!min_line_count(n_old.src, 6)) {
                    continue;
                }
                node n = strip_location(n_old);
                node n_normalized = normalize_node_to_type2(n);

                if (exact_buckets[n_normalized]?) {
                    exact_buckets[n_normalized] += [n_old];
                } else {
                    exact_buckets[n_normalized] = [n_old];
                }

                // Type 2 shouldn't be taken if its type , so type 1 has also be trackt
                if (exact_buckets_type1[n]?) {
                    exact_buckets_type1[n] += [n_old];
                } else {
                    exact_buckets_type1[n] = [n_old];
                }
                
            }            
            for (k <- exact_buckets_type1) {
                if (size(exact_buckets_type1[k]) >= 2) {
                    all_clones_type1 += exact_buckets_type1[k];
                }
            }
            // Each exactBucket with size >= 2 is a Type I clone class
            for (k <- exact_buckets) {
                if ((size(exact_buckets[k]) >= 2)) {
                    list[node] temp_list = [];
                    for (clone <- exact_buckets[k]) {
                        if (!(clone in all_clones_type1)) {
                            temp_list += clone;
                        }
                    }
                    if (size(temp_list) > 0) {
                        all_clones += [temp_list];
                    }
                }
            }
        }
    }

    all_clones = remove_child_clones_per_class(all_clones);

    return all_clones;
}

map[loc, int] get_last_line_numbers(list[Declaration] asts) {
    map[loc, int] file_last_lines = ();

    for (Declaration ast <- asts) {
        if (ast has src) {
            loc file_loc = ast.src;
            int last_line = file_loc.end.line;
            file_last_lines[file_loc] = last_line;
        }
    }

    return file_last_lines;
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

// This function counts all the lines, including the white lines
// and commetns to be able to find the last line
int count_all_line(loc location) {
    // starts as 1, as the function counts the new lines and that is always one less the the last line number.
    int count = 1;
	str content = readFile(location);

    list[str] lines = split("\n", content);
    for(i <- lines)
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
    map[str, int] lines_per_clone = ();
    map[loc, int] last_line_file = ();

    for (f <- files(model.containment), isCompilationUnit(f)) {
        int lines_in_file = compute_LOC(f);
        total_lines += lines_in_file;
        lines_per_file[f] = lines_in_file;

        last_line_file[f] = count_all_line(f);
    }

    for (clones <- clone_classes) {
        num class_size = size(clones);
        num loc_per_clone = compute_LOC(clones[0].src);
        if (loc_per_clone > biggest_clone_in_lines) {
            biggest_clone_in_lines = loc_per_clone;
            node biggest_clone = clones[0];
        }
        for (node clone_node <- clones) {
            // Get the file location for the clone
            if (loc source_loc := clone_node.src) {
                loc file_loc = source_loc; 
            
                if (file_loc.uri in lines_per_clone) {
                     lines_per_clone[file_loc.uri] += loc_per_clone; 
                } else {
                     lines_per_clone[file_loc.uri] = loc_per_clone;
                }
            } else {
                println("Warning: Clone node found without a source location field!");
            }
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

        // JSON ALWAYS gets written, terminal ouput not
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
    output += "\n  \"lines_per_clone\": {";

    hown = 0;
    first_class = true;

    for (f <- lines_per_clone) {
        shown += 1;

        if (!first_class) {
            output += ",\n";
        } else {
            output += "\n";
            first_class = false;
        }
        output += "    \"<f>\": <lines_per_clone[f]>";

        if (shown <= 5) {
            println("\nFile <f> has <lines_per_clone[f]> clone lines");
        } else if (shown == 6) {
            println("\n... (remaining clone line lengths omitted from console output)");
        }
    }

    output += "\n  },";
    output += "\n  \"last_line_per_file\": {";

    shown = 0;
    first_class = true;

    for (f <- last_line_file) {
        shown += 1;

        if (!first_class) {
            output += ",\n";
        } else {
            output += "\n";
            first_class = false;
        }
        output += "    \"<f>\": <last_line_file[f]>";

        if (shown <= 5) {
            println("File <f> has <last_line_file[f]> as last line number");
        } else if (shown == 6) {
            println("\n... (remaining file lengths omitted from console output)");
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

    output += "\n  }\n";
    output += "}\n";
    writeFile(json_output_location, output);
}

int main(int testArgument=0) {
    // loc folder_name = |file:///C:/Users/colin/Downloads/smallsql0.21_src/smallsql0.21_src/|;
    // loc folder_name = |file:///C:/Users/colin/Downloads/hsqldb-2.3.1/hsqldb-2.3.1/|;
    // loc folder_name = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/test_files|;
    loc folder_name = |file:///C:/Users/Mikev/Downloads/smallsql0.21_src/smallsql0.21_src|;
    //loc folder_name = |file:///C:/Users/Mikev/Downloads/hsqldb-2.3.1/hsqldb-2.3.1/|;
    //loc folder_name = |file:///C:/SE_master/rascall_series2_working/test_files|;
    
    //loc json_output_location = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/clone_report_type1.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/smallsq_clone_report_type1.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/hsqldb_clone_report_type1.json|;
    loc json_output_location = |file:///C:/SE_master/rascall_series2_working/smallsq_clone_report_type1_test.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/smallsq_clone_report_type2.json|;
    //loc json_output_location = |file:///C:/SE_master/rascall_series2_working/hsqldb_clone_report_type2.json|;

    list[Declaration] asts = getASTs(folder_name);
    list[list[node]] clones_type1 = find_clones_type2(asts, 25);
    write_and_print_report(clones_type1, folder_name, json_output_location);

    return testArgument;
}
