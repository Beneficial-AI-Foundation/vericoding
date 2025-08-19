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
    
    // Remove one instance of p from m to get the remaining elements
    var remaining := m - multiset{p};
    
    // Partition remaining elements based on pivot
    /* code modified by LLM (iteration 3): Fixed multiset comprehension syntax - used curly braces and && operator instead of parentheses and :: */
    pre := multiset{z | z in remaining && z <= p};
    post := multiset{z | z in remaining && z >= p};
}