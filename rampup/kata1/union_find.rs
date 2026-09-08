// union-find data structure
// parent stores the parent of each element
// rank is used to keep the trees shallow
#[derive(Debug)]
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    // create n separate sets
    fn new(n: usize) -> Self {
        Self {
            // parent = [0, 1, 2, 3, 4]
            // rank   = [0, 0, 0, 0, 0]
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    // find the root of x
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            let root = self.find(self.parent[x]);

            // path compression
            self.parent[x] = root;
        }

        self.parent[x]
    }

    // merge the sets containing a and b
    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);

        // already in the same set
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
}


// fn main() {
//     let mut uf = UnionFind::new(5);

//     uf.union(0, 1);
//     uf.union(1, 2);

//     println!("{:?}", uf);
//     println!("find(2) = {}", uf.find(2));
// }


// naive set-of-sets model used as a reference
// each inner Vec represents one set
#[derive(Debug)]
struct NaiveSets {
    sets: Vec<Vec<usize>>,
}

impl NaiveSets {
    // initially every element is in its own set
    fn new(n: usize) -> Self {
        Self {
            sets: (0..n).map(|x| vec![x]).collect(),
        }
    }

    // check whether a and b are in the same set
    fn same_set(&self, a: usize, b: usize) -> bool {
        self.sets.iter().any(|set| {
            set.contains(&a) && set.contains(&b)
        })
    }

    // merge the sets containing a and b
    fn union(&mut self, a: usize, b: usize) {
        // find the set containing a
        let ia = self
            .sets
            .iter()
            .position(|set| set.contains(&a))
            .unwrap();

        // find the set containing b
        let ib = self
            .sets
            .iter()
            .position(|set| set.contains(&b))
            .unwrap();

        // already in the same set
        if ia == ib {
            return;
        }

        // remove one set
        let other = self.sets.remove(ib);

        // removing ib may change the index of ia
        let target = if ib < ia {
            ia - 1
        } else {
            ia
        };

        // merge the removed set into the target set
        self.sets[target].extend(other);
    }
}

// test a fixed sequence of unions against the naive model
fn test_against_naive() {
    let n = 10;

    let mut uf = UnionFind::new(n);
    let mut naive = NaiveSets::new(n);

    let operations = [
        (0, 1),
        (2, 3),
        (1, 2),
        (5, 6),
        (6, 7),
        (3, 7),
    ];

    for (a, b) in operations {
        uf.union(a, b);
        naive.union(a, b);

        // compare every pair after each union
        for x in 0..n {
            for y in 0..n {
                assert_eq!(
                    uf.find(x) == uf.find(y),
                    naive.same_set(x, y),
                    "Mismatch for ({x}, {y}) after union({a}, {b})"
                );
            }
        }
    }
}

// run many pseudo-random union sequences against the naive model
fn property_test_against_naive() {
    let n = 20;

    // try 100 different seeds
    for seed in 0..100 {
        let mut uf = UnionFind::new(n);
        let mut naive = NaiveSets::new(n);

        let mut state = seed as u64 + 1;

        // perform 200 unions for each seed
        for _ in 0..200 {
            // simple deterministic pseudo-random generator
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1);

            let a = (state as usize) % n;

            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1);

            let b = (state as usize) % n;

            uf.union(a, b);
            naive.union(a, b);

            // both models should agree for every pair
            for x in 0..n {
                for y in 0..n {
                    assert_eq!(
                        uf.find(x) == uf.find(y),
                        naive.same_set(x, y),
                        "Mismatch for ({x}, {y}) after union({a}, {b}), seed={seed}"
                    );
                }
            }
        }
    }
}

// fn main() {
//     test_against_naive();
//     property_test_against_naive();

//     println!("Union-Find agrees with naive model.");
// }


// rustc --test union_find.rs -o union_find_test
#[cfg(test)]
mod tests {
    use super::*;

    // test the fixed sequence
    #[test]
    fn fixed_sequence_matches_naive_model() {
        test_against_naive();
    }

    // test many generated union sequences
    #[test]
    fn property_test_matches_naive_model() {
        property_test_against_naive();
    }
}