// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

//IMPL SearchRecursive
method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
    decreases j - i
{
    if i == j {
        k := i;
    } else if a[i] < x {
        k := i;
    } else {
        /* code modified by LLM (iteration 1): Calculate mid and ensure proper bounds */
        var mid := (i + j) / 2;
        assert i < j;
        assert i <= mid < j;
        
        if a[mid] >= x {
            /* code modified by LLM (iteration 1): Prove sorted property for recursive call */
            assert forall p, q :: mid + 1 <= p < q < j ==> a[p] >= a[q] by {
                forall p, q | mid + 1 <= p < q < j 
                    ensures a[p] >= a[q]
                {
                    assert i <= p < q < j;
                }
            }
            
            k := SearchRecursive(a, mid + 1, j, x);
            
            /* code modified by LLM (iteration 1): Prove first postcondition */
            assert forall r | i <= r < k :: a[r] >= x by {
                forall r | i <= r < k
                    ensures a[r] >= x
                {
                    if r <= mid {
                        assert i <= r <= mid;
                        assert i <= mid < mid + 1;
                        assert a[r] >= a[mid] >= x;
                    }
                }
            }
        } else {
            /* code modified by LLM (iteration 1): Handle case where a[mid] < x */
            assert a[mid] < x;
            
            /* code modified by LLM (iteration 1): Prove sorted property for left part */
            assert forall p, q :: i <= p < q < mid + 1 ==> a[p] >= a[q] by {
                forall p, q | i <= p < q < mid + 1
                    ensures a[p] >= a[q]
                {
                    assert i <= p < q <= mid;
                    if q <= mid {
                        assert i <= p < q < j;
                    }
                }
            }
            
            /* code modified by LLM (iteration 1): Prove elements from mid onwards are < x */
            assert forall r | mid <= r < j :: a[r] < x by {
                forall r | mid <= r < j
                    ensures a[r] < x
                {
                    if r == mid {
                        assert a[r] == a[mid] < x;
                    } else {
                        assert mid < r < j;
                        assert a[mid] >= a[r];
                        assert a[r] <= a[mid] < x;
                    }
                }
            }
            
            k := SearchRecursive(a, i, mid + 1, x);
            
            /* code modified by LLM (iteration 1): Prove second postcondition */
            assert forall r | k <= r < j :: a[r] < x by {
                forall r | k <= r < j
                    ensures a[r] < x
                {
                    if r < mid + 1 {
                        assert k <= r < mid + 1;
                    } else {
                        assert mid + 1 <= r < j;
                        assert mid <= r < j;
                    }
                }
            }
        }
    }
}

//ATOM SearchLoop
// Placeholder for SearchLoop atom - would be implemented if provided

//ATOM Test  
// Placeholder for Test atom - would be implemented if provided