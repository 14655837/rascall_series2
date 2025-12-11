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

// TODO rewrite this function!
public lrel[node,node] removeSymmetricPairs(lrel[node,node] clonePairs) {
    lrel[node,node] newClonePairs = [];
    for (pair <- clonePairs) {
        tuple[node, node] reversePair = <pair[1], pair[0]>;
        if (reversePair notin newClonePairs) {
            newClonePairs += pair;
        }
    }
    return newClonePairs;
}

public node stripLocation(node n) {
    // Recursively remove the `src` keyword parameter from the key node
    // (We keep the original node with src separate in `original`)
    n = unsetRec(n);
    return n;
}

public bool minLineCount(loc location, int lines) {
    int totalLines = location.end.line - location.begin.line;
	if (totalLines >= lines) {
        // println("Location <location> has <totalLines> lines.");
		return true;
	}
	return false;
}

// helper: true if inner is strictly inside outer (same file, smaller range)
public bool isInside(loc inner, loc outer) {
    return inner.scheme == outer.scheme
        && inner.authority == outer.authority
        && inner.path == outer.path
        && outer.offset <= inner.offset
        && outer.offset + outer.length >= inner.offset + inner.length
        && (inner.offset != outer.offset || inner.length != outer.length);
}

// "Similar" to your Java approach: treat every clone node as a candidate
// and drop those that live *inside* another clone.
public list[list[node]] removeChildClonesPerClass(list[list[node]] cloneClasses) {
    list[list[node]] result = [];

    for (cls <- cloneClasses) {
        set[node] toRemove = {};

        for (n <- cls) {
            // check if n is inside some *other* node in the same clone classes
            for (otherCls <- cloneClasses) {
                for (m <- otherCls) {
                    if (n == m || !(m has src)) {
                        continue;
                    }
                    if (isInside(n.src, m.src)) {
                        toRemove += { n };
                        break;
                    }
                }
                if (n in toRemove) {
                    break;
                }
            }
        }

        list[node] filtered = [ n | n <- cls, !(n in toRemove) ];
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
    int doneBuckets = 0;
    int totalBuckets = size(bucket);

    // Step 2: for each mass-bucket, group by exact subtree
    for (b <- bucket) {
        doneBuckets += 1;
        if (doneBuckets % 50 == 0) {
            println("Processed <doneBuckets>/<totalBuckets> buckets...");
        }

        int bucketSize = size(bucket[b]);
        if (bucketSize >= 2) {

            // group by exact subtree value inside the mass bucket
            map[node, list[node]] exactBuckets = ();
            for (n_old <- bucket[b]) {
                if (!(n_old has src)) {
                    continue;
                }
                if (!minLineCount(n_old.src, 6)) {
                    continue;
                }
                node n = stripLocation(n_old);
                // println("n: <n>\n\n\n");
                // println("Processing node with src: <n_old.src>");
                if (exactBuckets[n]?) {
                    exactBuckets[n] += [n_old];
                } else {
                    exactBuckets[n] = [n_old];
                }
                
            }            

            // Each exactBucket with size >= 2 is a Type I clone class
            for (k <- exactBuckets) {
                if (size(exactBuckets[k]) >= 2) {
                    // optionally show some structure
                    all_clones += [exactBuckets[k]];
                }
            }
        }
    }

    all_clones = removeChildClonesPerClass(all_clones);

    return all_clones;
}

public int computeLOC(loc location){
	int count = 0;
	str content = readFile(location);
	commentFree = visit(content){
		case /(\/\*[\s\S]*?\*\/|\/\/[\s\S]*?(\n|\r))/ => ""
	}
	list[str] lines = split("\n",commentFree);
	for( i <- lines, trim(i) != "")
		count += 1;
	return count;
}

void writeAndPrintReport(list[list[node]] cloneClasses, loc projectLocation, loc jsonOutputLocation) {

    // calculate % of duplicate lines and biggest clone

    num totalLines = 0;
    num duplicateLines = 0;
    num biggestCloneInLines = 0;

    M3 model = createM3FromMavenProject(projectLocation);

    for (f <- files(model.containment), isCompilationUnit(f)) {
        totalLines += computeLOC(f);
    }

    for (clones <- cloneClasses) {
        num classSize = size(clones);
        num loc_per_clone = computeLOC(clones[0].src);
        if (loc_per_clone > biggestCloneInLines) {
            biggestCloneInLines = loc_per_clone;
            node biggestClone = clones[0];
        }
        duplicateLines += loc_per_clone * classSize;
    }

    num duplicatePercentage = (duplicateLines / totalLines) * 100.0;

    // calculate number of clones
    num totalClones = 0;
    for (clones <- cloneClasses) {
        totalClones += size(clones);
    }

    // calculate number of clone classes
    num totalCloneClasses = size(cloneClasses);


    // print and write report

    str output = "";

    output += "{";
    output += "\n  \"totalLines\": <totalLines>,";
    output += "\n  \"duplicateLines\": <duplicateLines>,";
    output += "\n  \"duplicatePercentage\": <duplicatePercentage>,";
    output += "\n  \"totalClones\": <totalClones>,";
    output += "\n  \"totalCloneClasses\": <totalCloneClasses>,";
    output += "\n  \"biggestCloneInLines\": <biggestCloneInLines>,";

    println("Total lines of code: <totalLines>");
    println("Total duplicate lines of code: <duplicateLines> (<duplicatePercentage>% )");
    println("Total number of clones: <totalClones>");
    println("Total number of clone classes: <totalCloneClasses>");
    println("Biggest clone class size in lines: <biggestCloneInLines>");

    println("=== Example clone classes ===");

    // start JSON field for example clone classes
    output += "\n  \"exampleCloneClasses\": {";

    int shown = 0;
    bool firstClass = true;

    for (list[node] cls <- cloneClasses) {
        shown += 1;

        // JSON ALWAYS gets written
        if (!firstClass) {
            output += ",\n";
        } else {
            output += "\n";
            firstClass = false;
        }

        // JSON: always output every clone class
        output += "    \"CloneClass<shown>\": [";

        bool firstClone = true;
        for (node c <- cls) {
            if (!firstClone) {
                output += ", ";
            } else {
                firstClone = false;
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

    // close exampleCloneClasses object and the top-level JSON object
    output += "\n  }\n";
    output += "}\n";
    writeFile(jsonOutputLocation, output);
}



int main(int testArgument=0) {
    loc folder_name = |file:///C:/Users/colin/Downloads/smallsql0.21_src/smallsql0.21_src/|;
    // loc folder_name = |file:///C:/Users/colin/Downloads/hsqldb-2.3.1/hsqldb-2.3.1/|;
    // loc folder_name = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/test_files|;
    loc jsonOutputLocation = |file:///C:/Users/colin/Desktop/rascal/rascall_series2/clone_report_type1.json|;
    list[Declaration] asts = getASTs(folder_name);
    list[list[node]] clones_type1 = find_clones_type1(asts, 5);

    writeAndPrintReport(clones_type1, folder_name, jsonOutputLocation);

    return testArgument;
}
