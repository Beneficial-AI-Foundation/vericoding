//IMPL Partition
method Partition( m: multiset<int> )
    returns( pre: multiset<int>, p: int, post: multiset<int> )
  requires |m| > 0
  ensures p in m
  ensures m == pre+multiset{p}+post
  ensures forall z | z in pre :: z <= p
  ensures forall z | z in post :: z >= p
{
    // Choose any element from m as pivot
    p :| p in m;
    
    // Remove p from m to get remaining elements
    var remaining := m - multiset{p};
    
    // Initialize empty multisets
    pre := multiset{};
    post := multiset{};
    
    /* code modified by LLM (iteration 3): Use a working set approach instead of sequence conversion */
    var working := remaining;
    
    while working != multiset{}
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
        invariant pre + post + working == remaining
        decreases |working|
    {
        var elem :| elem in working;
        working := working - multiset{elem};
        
        if elem <= p {
            pre := pre + multiset{elem};
        } else {
            post := post + multiset{elem};
        }
    }
    
    /* code modified by LLM (iteration 3): Final assertion to establish postcondition */
    assert pre + post == remaining;
    assert m == multiset{p} + remaining;
}