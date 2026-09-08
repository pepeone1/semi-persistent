use std::collections::HashMap;

type ClassId = usize;


#[derive(Debug)]
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            // parent = [0, 1, 2, 3, 4]
            // rank   = [0, 0, 0, 0, 0]
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            let root = self.find(self.parent[x]);
            // path compression
            self.parent[x] = root;
        }
        self.parent[x]
    }


    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        
        // in the same set
        if ra == rb {
            return;
        }

        // union by rank
        // attach the lower-rank tree under the higher-rank tree
        // if the ranks are equal, choose one as the root and increment its rank
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
        }
    }

    // make a new set for new e-class, return the new class id
    fn make_set(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        id
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ENode {
    op: String,
    children: Vec<ClassId>,
}

struct EGraph {
    // e-class equality
    uf: UnionFind,

    // hash-consing table:
    // canonical e-node -> e-class
    memo: HashMap<ENode, ClassId>,

    // all nodes belonging to each e-class.
    classes: Vec<Vec<ENode>>,
}



impl EGraph {
    fn new() -> Self {
        Self {
            uf: UnionFind::new(0),
            memo: HashMap::new(),
            classes: Vec::new(),
        }
    }

    fn add(&mut self, op: &str, children: Vec<ClassId>) -> ClassId {
        // canonicalize children
        let canonical_children: Vec<ClassId> = children
            .into_iter()
            .map(|child| self.uf.find(child))
            .collect();

        let node = ENode {
            op: op.to_string(),
            children: canonical_children,
        };

        // hash-consing: reuse an existing identical node
        if let Some(&class_id) = self.memo.get(&node) {
            return self.uf.find(class_id);
        }

        // create a new e-class
        let class_id = self.uf.make_set();

        self.classes.push(vec![node.clone()]);
        self.memo.insert(node, class_id);

        class_id
    }

    fn find(&mut self, id: ClassId) -> ClassId {
        self.uf.find(id)
    }

    fn union(&mut self, a: ClassId, b: ClassId) {
        self.uf.union(a, b);
    }

    fn rebuild(&mut self) {
        // keep rebuilding until congruence is fully restored
        // a merge may create new equalities, so one pass may not be enough
        loop {
            let mut changed = false;
            let mut new_memo: HashMap<ENode, ClassId> = HashMap::new();

            for class_id in 0..self.classes.len() {
                let canonical_class = self.uf.find(class_id);

                let nodes = self.classes[class_id].clone();

                for node in nodes {
                    // canonicalize the children
                    // replace every child class with its current representative
                    let canonical_children: Vec<ClassId> = node
                        .children
                        .iter()
                        .map(|&child| self.uf.find(child))
                        .collect();

                    let canonical_node = ENode {
                        op: node.op.clone(),
                        children: canonical_children,
                    };

                    // same canonical node -> merge their e-classes
                    if let Some(&other_class) = new_memo.get(&canonical_node) {
                        let a = self.uf.find(canonical_class);
                        let b = self.uf.find(other_class);

                        if a != b {
                            self.uf.union(a, b);
                            changed = true;
                        }
                    } else {
                        // add the node to the new hash-consing table
                        new_memo.insert(canonical_node, canonical_class);
                    }
                }
            }

            // replace the old hash-consing table
            self.memo = new_memo;

            // stop when no more e-classes are merged
            if !changed {
                break;
            }
        }
    }
}



// rustc --test toy_egraph.rs -o toy_egraph_test
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rebuild_restores_congruence() {
        let mut egraph = EGraph::new();

        // 2 different classes
        let a = egraph.add("a", vec![]);
        let b = egraph.add("b", vec![]);

        // f(a) and f(b) while a and b are still different
        let fa = egraph.add("f", vec![a]);
        let fb = egraph.add("f", vec![b]);
        assert_ne!(egraph.find(fa), egraph.find(fb));

        // merge a and b
        egraph.union(a, b);

        // BUG WITHOUT REBUILD:
        // a == b, but f(a) and f(b) are still in different e-classes
        assert_eq!(egraph.find(a), egraph.find(b));
        assert_ne!(egraph.find(fa), egraph.find(fb));

        // rebuild
        egraph.rebuild();

        // now f(a) == f(b)
        assert_eq!(egraph.find(fa), egraph.find(fb));
    }
}