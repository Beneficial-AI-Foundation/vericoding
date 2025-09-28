use vstd::prelude::*;

verus! {

// verifies
// check that string between indexes low and high-1 are sorted
spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

// <vc-helpers>
// No helpers needed for this example.
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    let x = a@[0];
    let y = a@[1];
    let z = a@[2];

    if x <= y {
        if y <= z {
            proof {
                assert(x == a@[0]);
                assert(y == a@[1]);
                assert(z == a@[2]);
                assert(x <= y);
                assert(y <= z);
                assert(x <= z);
                assert(seq![x, y, z].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
            }
            return seq![x, y, z];
        } else {
            if x <= z {
                proof {
                    assert(x == a@[0]);
                    assert(y == a@[1]);
                    assert(z == a@[2]);
                    assert(x <= y);
                    assert(!(y <= z)); // y > z
                    assert(x <= z);
                    assert(seq![x, z, y].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
                }
                return seq![x, z, y];
            } else {
                proof {
                    assert(x == a@[0]);
                    assert(y == a@[1]);
                    assert(z == a@[2]);
                    assert(x <= y);
                    assert(!(y <= z)); // y > z
                    assert(!(x <= z)); // x > z
                    assert(seq![z, x, y].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
                    // show z <= x and x <= y to establish sortedness
                    assert(z <= x);
                    assert(x <= y);
                }
                return seq![z, x, y];
            }
        }
    } else {
        if x <= z {
            proof {
                assert(x == a@[0]);
                assert(y == a@[1]);
                assert(z == a@[2]);
                assert(!(x <= y)); // x > y
                assert(x <= z);
                assert(seq![y, x, z].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
                // show y <= x and x <= z to establish sortedness
                assert(y <= x);
                assert(x <= z);
            }
            return seq![y, x, z];
        } else {
            if y <= z {
                proof {
                    assert(x == a@[0]);
                    assert(y == a@[1]);
                    assert(z == a@[2]);
                    assert(!(x <= y)); // x > y
                    assert(!(x <= z)); // x > z
                    assert(y <= z);
                    assert(seq![y, z, x].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
                    // show y <= z and z <= x to establish sortedness
                    assert(y <= z);
                    assert(z <= x);
                }
                return seq![y, z, x];
            } else {
                proof {
                    assert(x == a@[0]);
                    assert(y == a@[1]);
                    assert(z == a@[2]);
                    assert(!(x <= y)); // x > y
                    assert(!(x <= z)); // x > z
                    assert(!(y <= z)); // y > z
                    assert(seq![z, y, x].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
                    // show z <= y and y <= x to establish sortedness
                    assert(z <= y);
                    assert(y <= x);
                }
                return seq![z, y, x];
            }
        }
    }
}
// </vc-code>

fn main() {
}

}