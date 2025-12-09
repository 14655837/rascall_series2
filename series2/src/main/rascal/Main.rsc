module Main

import util::IDEServices;
import lang::java::m3::Core;
import lang::java::m3::AST;

import IO;
import List;
import Set;
import String;
import Map;

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

list[node] find_clones_type1(list[Declaration] asts, int treshold) {
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

    similairity_treshhold =  1.0;

    // TODO rewrite this function!
    list[node] all_clones = [];
    for (b <- bucket) {
        if (size(bucket[b]) >= 2) {
            lrel[node left, node right] bucket_pairs = [];
            bucket_pairs += bucket[b] * bucket[b];
            //don't compare with itself
            bucket_pairs = [pair | pair <- bucket_pairs, pair.left != pair.right];
            //remove one of the the symmetric pairs, otherwise u count a clone double
            bucket_pairs = removeSymmetricPairs(bucket_pairs);

            for (pair <- bucket_pairs) {
                similairity_pair = similarity(pair[0], pair[1]);
                if (similairity_pair >= similairity_treshhold) {
                    all_clones += pair[0];
                    all_clones += pair[1];
                }
            }
        }   
    }
    
    return all_clones;
}

int main(int testArgument=0) {
    loc folder_name = |file:///C:/Users/colin/Downloads/smallsql0.21_src/smallsql0.21_src/|;;
    //loc folder_name = |file:///C:/Users/Mikev/Downloads/smallsql0.21_src/smallsql0.21_src|;
    list[Declaration] asts = getASTs(folder_name);
    list[node] clones_type1 = find_clones_type1(asts, 6);
    int sum_clones_type1 = size(clones_type1);

    println("argument: <sum_clones_type1>");
    return testArgument;
}
