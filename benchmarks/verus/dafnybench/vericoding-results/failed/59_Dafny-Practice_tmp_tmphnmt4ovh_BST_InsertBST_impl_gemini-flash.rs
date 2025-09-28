use vstd::prelude::*;

verus! {

pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

spec fn numbers_in_tree(t: Tree) -> Set<int> {
    numbers_in_sequence(inorder(t))
}

spec fn numbers_in_sequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| q.contains(x))
}

spec fn bst(t: Tree) -> bool {
    ascending(inorder(t))
}

spec fn inorder(t: Tree) -> Seq<int>
    decreases t
{
    match t {
        Tree::Empty => seq![],
        Tree::Node(n, left, right) => inorder(*left) + seq![n] + inorder(*right)
    }
}

spec fn ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn no_duplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

// <vc-helpers>
spec fn num_elements(t: Tree) -> nat {
    match t {
        Tree::Empty => 0,
        Tree::Node(_, left, right) => 1 + num_elements(*left) + num_elements(*right),
    }
}

proof fn lemma_inorder_len_num_elements(t: Tree)
    ensures inorder(t).len() == num_elements(t)
    decreases t
{
    match t {
        Tree::Empty => {
            assert(inorder(Tree::Empty) == seq![]);
            assert(inorder(Tree::Empty).len() == 0);
            assert(num_elements(Tree::Empty) == 0);
        }
        Tree::Node(_, left, right) => {
            lemma_inorder_len_num_elements(*left);
            lemma_inorder_len_num_elements(*right);
            assert(inorder(t).len() == inorder(*left).len() + 1 + inorder(*right).len());
            assert(inorder(*left).len() == num_elements(*left));
            assert(inorder(*right).len() == num_elements(*right));
            assert(inorder(t).len() == num_elements(*left) + 1 + num_elements(*right));
            assert(num_elements(t) == num_elements(*left) + 1 + num_elements(*right));
        }
    }
}

proof fn lemma_numbers_in_tree_inorder_elements(t: Tree)
    ensures forall |x: int| numbers_in_tree(t).contains(x) <==> inorder(t).contains(x)
    decreases t
{
    match t {
        Tree::Empty => {
            assert(numbers_in_tree(Tree::Empty) =~= Set::empty());
            assert(inorder(Tree::Empty) == seq![]);
            assert(numbers_in_sequence(seq![]) =~= Set::empty());
        }
        Tree::Node(_, left, right) => {
            lemma_numbers_in_tree_inorder_elements(*left);
            lemma_numbers_in_tree_inorder_elements(*right);

            assert forall |x: int| #[trigger] numbers_in_sequence(inorder(*left)).contains(x) <==> inorder(*left).contains(x) by {
                assert (numbers_in_sequence(inorder(*left)) =~= numbers_in_tree(*left));
            }
            assert forall |x: int| #[trigger] numbers_in_sequence(inorder(*right)).contains(x) <==> inorder(*right).contains(x) by {
                assert (numbers_in_sequence(inorder(*right)) =~= numbers_in_tree(*right));
            }

            assert forall |v: int| numbers_in_tree(t).contains(v) <==> (numbers_in_tree(*left).contains(v) || v == t.get_Node_0() || numbers_in_tree(*right).contains(v)) by {
                assert(numbers_in_tree(t) =~= numbers_in_sequence(inorder(*left) + seq![t.get_Node_0()] + inorder(*right)));
                assert(numbers_in_sequence(inorder(*left) + seq![t.get_Node_0()] + inorder(*right)) =~= numbers_in_sequence(inorder(*left)).union(Set::singleton(t.get_Node_0())).union(numbers_in_sequence(inorder(*right))));
            }

            assert forall |v: int| inorder(t).contains(v) <==> (inorder(*left).contains(v) || v == t.get_Node_0() || inorder(*right).contains(v)) by {
            }

            assert forall |x: int| numbers_in_tree(t).contains(x) <==> inorder(t).contains(x) by {
                let Tree::Node(n_val, left, right) = t;
                if numbers_in_tree(t).contains(x) {
                    if numbers_in_tree(*left).contains(x) {
                        assert(inorder(*left).contains(x));
                        assert(inorder(t).contains(x));
                    } else if x == n_val {
                        assert(inorder(t).contains(x));
                    } else {
                        assert(numbers_in_tree(*right).contains(x));
                        assert(inorder(*right).contains(x));
                        assert(inorder(t).contains(x));
                    }
                } else {
                    // !numbers_in_tree(t).contains(x)
                    // => !(numbers_in_tree(*left).contains(x) || x == t.get_Node_0() || numbers_in_tree(*right).contains(x))
                    // => !numbers_in_tree(*left).contains(x) && x != t.get_Node_0() && !numbers_in_tree(*right).contains(x)
                    // => !inorder(*left).contains(x) && x != t.get_Node_0() && !inorder(*right).contains(x)
                    assert(!inorder(t).contains(x));
                }
            }
        }
    }
}

spec fn min_of_seq(s: Seq<int>) -> int
    requires s.len() > 0 && ascending(s)
{
    s[0]
}

spec fn max_of_seq(s: Seq<int>) -> int
    requires s.len() > 0 && ascending(s)
{
    s[s.len() - 1]
}
// </vc-helpers>

// <vc-spec>
fn insert_bst(t0: Tree, x: int) -> (t: Tree)
    requires 
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures 
        bst(t) && numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x)
// </vc-spec>
// <vc-code>
{
    match t0 {
        Tree::Empty => {
            assert(bst(Tree::Empty)); // From precondition
            assert(numbers_in_tree(Tree::Empty) =~= Set::empty());
            assert(numbers_in_tree(Tree::Empty).insert(x) =~= Set::singleton(x));

            let t = Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty));
            assert(inorder(t) == seq![x]);
            assert(ascending(seq![x]));
            assert(bst(t));
            assert(numbers_in_tree(t) =~= Set::singleton(x));
            assert(numbers_in_tree(t) =~= numbers_in_tree(Tree::Empty).insert(x));
            t
        }
        Tree::Node(n, left_box, right_box) => {
            let left = *left_box;
            let right = *right_box;

            let inv_inorder = inorder(left);
            let inv_inorder_plus_n_plus_inorder_right = inorder(left) + seq![n] + inorder(right); // inorder(t0)
            
            // Proof that pre_condition establishes relevant properties for recursion
            proof {
                assert(bst(t0)); // From precondition
                assert(ascending(inorder(t0)));
                assert(no_duplicates(inorder(t0))) by {
                    assert forall |i: int, j: int| 0 <= i < j < inorder(t0).len() implies inorder(t0)[i] < inorder(t0)[j] by {
                        assert(ascending(inorder(t0)));
                    }
                    assert(no_duplicates(inorder(t0)));
                }

                lemma_numbers_in_tree_inorder_elements(t0);
                assert(!numbers_in_tree(t0).contains(x)); // From precondition
                assert(!inorder(t0).contains(x)) by { // Required for no_duplicates property for new tree
                    assert forall |v: int| numbers_in_tree(t0).contains(v) <==> inorder(t0).contains(v) by {
                        lemma_numbers_in_tree_inorder_elements(t0);
                    }
                }

                assert(bst(left)) by {
                    assert(ascending(inorder(left))) by {
                        assert(ascending(inorder(t0)));
                        assert(inorder(t0) == inorder(left) + seq![n] + inorder(right));
                        assert forall |i: int, j: int| 0 <= i < j < inorder(left).len() implies inorder(left)[i] < inorder(left)[j] by {
                            assert(i < inorder(left).len());
                            assert(j < inorder(left).len());
                            assert(inorder(left)[i] == inorder(t0)[i]);
                            assert(inorder(left)[j] == inorder(t0)[j]);
                            assert(inorder(left)[i] < inorder(left)[j]);
                        }
                    }
                }
                assert(bst(right)) by {
                    assert(ascending(inorder(right))) by {
                        assert(ascending(inorder(t0)));
                        assert(inorder(t0) == inorder(left) + seq![n] + inorder(right));
                        assert forall |i: int, j: int| 0 <= i < j < inorder(right).len() implies inorder(right)[i] < inorder(right)[j] by {
                            let offset = inorder(left).len() + 1;
                            assert(i < inorder(right).len());
                            assert(j < inorder(right).len());
                            assert(inorder(right)[i] == inorder(t0)[offset + i]);
                            assert(inorder(right)[j] == inorder(t0)[offset + j]);
                            assert(inorder(right)[i] < inorder(right)[j]);
                        }
                    }
                }

                // Check numbers_in_tree(left) / numbers_in_tree(right) properties
                assert(!numbers_in_tree(left).contains(x)) by {
                    assert forall |v: int| numbers_in_tree(left).contains(v) <==> inorder(left).contains(v) by {
                        lemma_numbers_in_tree_inorder_elements(left);
                    }
                    assert(!inorder(left).contains(x)) by {
                        assert(!inorder(t0).contains(x));
                        assert(inorder(t0) == inorder(left) + seq![n] + inorder(right));
                    }
                }
                assert(!numbers_in_tree(right).contains(x)) by {
                    assert forall |v: int| numbers_in_tree(right).contains(v) <==> inorder(right).contains(v) by {
                        lemma_numbers_in_tree_inorder_elements(right);
                    }
                    assert(!inorder(right).contains(x)) by {
                        assert(!inorder(t0).contains(x));
                        assert(inorder(t0) == inorder(left) + seq![n] + inorder(right));
                    }
                }

                // Prove n is not x
                assert(n != x) by {
                    assert(!numbers_in_tree(t0).contains(x));
                    assert(numbers_in_tree(t0).contains(n));
                }
            }

            if x < n {
                let t_prime = insert_bst(left, x);
                let res = Tree::Node(n, Box::new(t_prime), Box::new(right));

                proof {
                    assert(bst(t_prime));
                    assert(numbers_in_tree(t_prime) =~= numbers_in_tree(left).insert(x));

                    assert(inorder(res) == inorder(t_prime) + seq![n] + inorder(right));
                    
                    // Verify bst(res)
                    assert(ascending(inorder(res))) by {
                        assert(ascending(inorder(t_prime)));
                        assert(ascending(inorder(right)));

                        assert(inorder(left) + seq![n] + inorder(right) == inorder(t0));
                        assert(ascending(inorder(t0)));
                        if inorder(left).len() > 0 {
                            assert(inorder(left).last() < n) by {
                                assert(max_of_seq(inorder(left)) == inorder(left).last());
                                assert(ascending(inorder(left)));
                                let idx_last_left = inorder(left).len() -1;
                                assert(idx_last_left < inorder(t0).len());
                                assert(inorder(left).last() == inorder(t0)[idx_last_left]);
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(idx_last_left < inorder(left).len()); // Check the indices
                                assert(inorder(t0).len() > inorder(left).len());
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(inorder(left).len() == idx_last_left + 1);
                                assert(idx_last_left < inorder(left).len());
                                assert(inorder(t0)[idx_last_left] < inorder(t0)[inorder(left).len()]);
                            }
                        }
                        if inorder(right).len() > 0 {
                             assert(n < inorder(right).first()) by {
                                assert(min_of_seq(inorder(right)) == inorder(right).first());
                                assert(ascending(inorder(right)));
                                let idx_first_right = inorder(left).len() + 1;
                                assert(idx_first_right < inorder(t0).len());
                                assert(inorder(right).first() == inorder(t0)[idx_first_right]);
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(inorder(left).len() < idx_first_right);
                                assert(inorder(t0)[inorder(left).len()] < inorder(t0)[idx_first_right]);
                            }
                        }

                        if inorder(t_prime).len() > 0 {
                            assert(inorder(t_prime).last() < n) by {
                                if inorder(left).len() == 0 { 
                                    assert(t_prime == Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty)));
                                    assert(inorder(t_prime) == seq![x]);
                                    assert(x < n); 
                                    assert(inorder(t_prime).last() == x);
                                    assert(inorder(t_prime).last() < n);
                                } else { 
                                    assert(inorder(t_prime).last() == max_of_seq(inorder(t_prime)));
                                    assert(inorder(left).last() == max_of_seq(inorder(left)));
                                    assert(ascending(inorder(t_prime)));
                                    assert(ascending(inorder(left)));

                                    if x > inorder(left).last() {
                                        // This case happens if x is inserted and becomes the largest element in the new left subtree
                                        assert(inorder(t_prime).last() == x);
                                        assert(x < n);
                                    } else {
                                        // This case happens if x is inserted and is smaller than (or equal to if duplicates allowed) the current largest in left subtree
                                        assert(inorder(t_prime).last() == inorder(left).last());
                                        assert(inorder(left).last() < n);
                                    }
                                }
                            };
                        }

                        assert forall |i: int, j: int| 0 <= i < j < inorder(res).len() implies inorder(res)[i] < inorder(res)[j] by {
                            let len_t_prime = inorder(t_prime).len();
                            let len_n_val = 1;

                            if j < len_t_prime { 
                                assert(inorder(res)[i] == inorder(t_prime)[i]);
                                assert(inorder(res)[j] == inorder(t_prime)[j]);
                                assert(inorder(t_prime)[i] < inorder(t_prime)[j]);
                            } else if i >= len_t_prime + len_n_val { 
                                assert(inorder(res)[i] == inorder(right)[i - (len_t_prime + len_n_val)]);
                                assert(inorder(res)[j] == inorder(right)[j - (len_t_prime + len_n_val)]);
                                assert(inorder(right)[i - (len_t_prime + len_n_val)] < inorder(right)[j - (len_t_prime + len_n_val)]);
                            } else if i < len_t_prime && j == len_t_prime { 
                                assert(inorder(res)[i] == inorder(t_prime)[i]);
                                assert(inorder(res)[j] == n);
                                if inorder(t_prime).len() > 0 {
                                    assert(inorder(t_prime).last() < n);
                                    assert(inorder(res)[i] <= inorder(t_prime).last());
                                } else {
                                    assert(x < n);
                                }
                                assert(inorder(res)[i] < n);
                            } else if i < len_t_prime && j > len_t_prime { 
                                assert(inorder(res)[i] == inorder(t_prime)[i]);
                                assert(inorder(res)[j] == inorder(right)[j - (len_t_prime + len_n_val)]);
                                if inorder(t_prime).len() > 0 {
                                    assert(inorder(t_prime).last() < n);
                                    assert(inorder(res)[i] <= inorder(t_prime).last());
                                } else {
                                    assert(x < n);
                                }
                                if inorder(right).len() > 0 {
                                    assert(n < inorder(right).first());
                                    assert(n < inorder(res)[j]);
                                }
                                assert(inorder(res)[i] < inorder(res)[j]);
                            } else if i == len_t_prime && j > len_t_prime { 
                                assert(inorder(res)[i] == n);
                                assert(inorder(res)[j] == inorder(right)[j - (len_t_prime + len_n_val)]);
                                if inorder(right).len() > 0 {
                                    assert(n < inorder(right).first());
                                    assert(n < inorder(res)[j]);
                                }
                            }
                        }
                    }
                    assert(bst(res));

                    // Verify numbers_in_tree(res) =~= numbers_in_tree(t0).insert(x)
                    lemma_numbers_in_tree_inorder_elements(res);
                    lemma_numbers_in_tree_inorder_elements(t_prime);
                    lemma_numbers_in_tree_inorder_elements(right);

                    assert(inorder(res) == inorder(t_prime) + seq![n] + inorder(right));
                    assert(numbers_in_tree(res) =~= numbers_in_sequence(inorder(res)));
                    assert(numbers_in_sequence(inorder(res)) =~= numbers_in_sequence(inorder(t_prime)).union(Set::singleton(n)).union(numbers_in_sequence(inorder(right))));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(t_prime).union(Set::singleton(n)).union(numbers_in_tree(right)));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(left).insert(x).union(Set::singleton(n)).union(numbers_in_tree(right)));
                    assert(numbers_in_tree(t0) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right)));
                    
                    assert(!numbers_in_tree(right).contains(x));
                    assert(n != x);

                    assert(numbers_in_tree(t0).insert(x) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right)).insert(x));
                    assert(numbers_in_tree(t0).insert(x) =~= (numbers_in_tree(left).insert(x)).union(Set::singleton(n)).union(numbers_in_tree(right)));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(t0).insert(x));
                }
                res
            } else { // x > n, because x != n
                let t_prime = insert_bst(right, x);
                let res = Tree::Node(n, Box::new(left), Box::new(t_prime));

                proof {
                    assert(bst(t_prime));
                    assert(numbers_in_tree(t_prime) =~= numbers_in_tree(right).insert(x));

                    assert(inorder(res) == inorder(left) + seq![n] + inorder(t_prime));

                    // Verify bst(res)
                    assert(ascending(inorder(res))) by {
                        assert(ascending(inorder(left)));
                        assert(ascending(inorder(t_prime)));
                        
                        assert(inorder(left) + seq![n] + inorder(right) == inorder(t0));
                        assert(ascending(inorder(t0)));
                        if inorder(left).len() > 0 {
                            assert(inorder(left).last() < n) by {
                                assert(max_of_seq(inorder(left)) == inorder(left).last());
                                assert(ascending(inorder(left)));
                                let idx_last_left = inorder(left).len() -1;
                                assert(idx_last_left < inorder(t0).len());
                                assert(inorder(left).last() == inorder(t0)[idx_last_left]);
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(idx_last_left < inorder(left).len()); // Check the indices
                                assert(inorder(t0).len() > inorder(left).len());
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(inorder(left).len() == idx_last_left + 1);
                                assert(idx_last_left < inorder(left).len());
                                assert(inorder(t0)[idx_last_left] < inorder(t0)[inorder(left).len()]);
                            }
                        }
                        if inorder(right).len() > 0 {
                             assert(n < inorder(right).first()) by {
                                assert(min_of_seq(inorder(right)) == inorder(right).first());
                                assert(ascending(inorder(right)));
                                let idx_first_right = inorder(left).len() + 1;
                                assert(idx_first_right < inorder(t0).len());
                                assert(inorder(right).first() == inorder(t0)[idx_first_right];
                                assert(n == inorder(t0)[inorder(left).len()]);
                                assert(inorder(left).len() < idx_first_right);
                                assert(inorder(t0)[inorder(left).len()] < inorder(t0)[idx_first_right]);
                            }
                        }
                        if inorder(t_prime).len() > 0 {
                            assert(n < inorder(t_prime).first()) by {
                              if inorder(right).len() == 0 { 
                                  assert(t_prime == Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty)));
                                  assert(inorder(t_prime) == seq![x]);
                                  assert(x > n); 
                                  assert(inorder(t_prime).first() == x);
                                  assert(inorder(t_prime).first() > n);
                              } else { 
                                  assert(inorder(t_prime).first() == min_of_seq(inorder(t_prime)));
                                  assert(inorder(right).first() == min_of_seq(inorder(right)));
                                  assert(ascending(inorder(t_prime)));
                                  assert(ascending(inorder(right)));
                                  if x < inorder(right).first() {
                                      // This case happens if x is inserted and becomes the smallest element in the new right subtree
                                      assert(inorder(t_prime).first() == x);
                                      assert(x > n); 
                                  } else {
                                      // This case happens if x is inserted and is larger than (or equal to if duplicates allowed) the current smallest in right subtree
                                      assert(inorder(t_prime).first() == inorder(right).first());
                                      assert(inorder(right).first() > n); 
                                  }
                              }
                            };
                        }

                        assert forall |i: int, j: int| 0 <= i < j < inorder(res).len() implies inorder(res)[i] < inorder(res)[j] by {
                            let len_left = inorder(left).len();
                            let len_n_val = 1;

                            if j < len_left { 
                                assert(inorder(res)[i] == inorder(left)[i]);
                                assert(inorder(res)[j] == inorder(left)[j]);
                                assert(inorder(left)[i] < inorder(left)[j]);
                            } else if i >= len_left + len_n_val { 
                                assert(inorder(res)[i] == inorder(t_prime)[i - (len_left + len_n_val)]);
                                assert(inorder(res)[j] == inorder(t_prime)[j - (len_left + len_n_val)]);
                                assert(inorder(t_prime)[i - (len_left + len_n_val)] < inorder(t_prime)[j - (len_left + len_n_val)]);
                            } else if i < len_left && j == len_left { 
                                assert(inorder(res)[i] == inorder(left)[i]);
                                assert(inorder(res)[j] == n);
                                if inorder(left).len() > 0 {
                                    assert(inorder(left).last() < n); 
                                    assert(inorder(res)[i] <= inorder(left).last());
                                } else {
                                    // This branch is taken if inorder(left).len() is 0. 
                                    // In this specific case, i cannot be < len_left, so this if-else branch is unreachable.
                                    // No additional assert needed as it demonstrates unreachable code.
                                    // assert(false); 
                                }
                                assert(inorder(res)[i] < n);
                            } else if i < len_left && j > len_left { 
                                assert(inorder(res)[i] == inorder(left)[i]);
                                assert(inorder(res)[j] == inorder(t_prime)[j - (len_left + len_n_val)]);
                                if inorder(left).len() > 0 {
                                    assert(inorder(left).last() < n); 
                                    assert(inorder(res)[i] <= inorder(left).last());
                                } else {
                                    // unreachable
                                    // assert(false);
                                }
                                if inorder(t_prime).len() > 0 {
                                    assert(n < inorder(t_prime).first()); 
                                    assert(n < inorder(res)[j]);
                                }
                                assert(inorder(res)[i] < inorder(res)[j]);
                            } else if i == len_left && j > len_left { 
                                assert(inorder(res)[i] == n);
                                assert(inorder(res)[j] == inorder(t_prime)[j - (len_left + len_n_val)]);
                                if inorder(t_prime).len() > 0 {
                                    assert(n < inorder(t_prime).first());
                                    assert(n < inorder(res)[j]);
                                }
                            }
                        }
                    }
                    assert(bst(res));

                    // Verify numbers_in_tree(res) =~= numbers_in_tree(t0).insert(x)
                    lemma_numbers_in_tree_inorder_elements(res);
                    lemma_numbers_in_tree_inorder_elements(left);
                    lemma_numbers_in_tree_inorder_elements(t_prime);

                    assert(inorder(res) == inorder(left) + seq![n] + inorder(t_prime));
                    assert(numbers_in_tree(res) =~= numbers_in_sequence(inorder(res)));
                    assert(numbers_in_sequence(inorder(res)) =~= numbers_in_sequence(inorder(left)).union(Set::singleton(n)).union(numbers_in_sequence(inorder(t_prime))));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(t_prime)));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right).insert(x)));
                    assert(numbers_in_tree(t0) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right)));

                    assert(!numbers_in_tree(left).contains(x));
                    assert(n != x);

                    assert(numbers_in_tree(t0).insert(x) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right)).insert(x));
                    assert(numbers_in_tree(t0).insert(x) =~= numbers_in_tree(left).union(Set::singleton(n)).union(numbers_in_tree(right).insert(x)));
                    assert(numbers_in_tree(res) =~= numbers_in_tree(t0).insert(x));
                }
                res
            }
        }
    }
}
// </vc-code>

fn main() {}

}