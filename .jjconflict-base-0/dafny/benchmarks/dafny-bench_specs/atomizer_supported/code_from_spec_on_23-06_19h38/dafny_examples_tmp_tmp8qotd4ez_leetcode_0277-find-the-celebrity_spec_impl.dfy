// Author: Shaobo He

//ATOM 
// Author: Shaobo He

predicate knows(a: int, b: int)

//ATOM 

predicate isCelebrity(n : int, i : int)
requires n >= 0 && 0 <= i < n;
{
    forall j :: 0 <= j < n && i != j ==> knows(j, i) && !knows(i, j)
}

//ATOM 

lemma knowerCannotBeCelebrity(n: int, i: int)
requires n >= 0 && 0 <= i < n
ensures (exists j :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
{}

//ATOM 

ghost method isCelebrityP(n: int, i: int) returns (r : bool)
requires n >= 0 && 0 <= i < n;
ensures r <==> isCelebrity(n, i);
{
    var j := 0;
    r := true;
    while j < n
    {
        if j != i {
            if !knows(j, i) || knows(i, j) {
                return false;
            }
        }
        j := j + 1;
    }
    return r;
}

//ATOM 

ghost method findCelebrity(n : int) returns (r : int)
requires 2 <= n <= 100;
ensures 0 <= r < n ==> isCelebrity(n, r);
ensures r == -1 ==> forall i :: 0 <= i < n ==> !isCelebrity(n, i);
{
    var candidate := 0;
    var i := 1;
    
    /* code modified by LLM (iteration 1): fixed loop invariants to track elimination of non-candidates */
    while i < n 
    invariant 1 <= i <= n
    invariant 0 <= candidate < i
    invariant forall j :: 0 <= j < candidate ==> knows(j, candidate)
    invariant forall j :: candidate < j < i ==> knows(candidate, j)
    {
        if knows(candidate, i) {
            candidate := i;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): used loop invariants to prove non-candidates cannot be celebrities */
    forall j | 0 <= j < n && j != candidate 
    ensures !isCelebrity(n, j)
    {
        if j < candidate {
            /* code modified by LLM (iteration 1): j knows candidate, so j cannot be celebrity */
            assert knows(j, candidate);
            if candidate != j {
                assert !isCelebrity(n, j);
            }
        } else {
            /* code modified by LLM (iteration 1): candidate knows j, so j cannot be celebrity */
            assert j > candidate;
            assert knows(candidate, j);
            if candidate != j {
                assert !isCelebrity(n, j);
            }
        }
    }
    
    var isCelebrityC := isCelebrityP(n, candidate);
    if isCelebrityC {
        r := candidate;
    } else {
        r := -1;
    }
}