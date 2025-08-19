// IMPL
// Höfundur spurningar: Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:   Alexander Guðmundsson
// Permalink lausnar:  https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

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
    
    // Initialize empty multisets
    pre := multiset{};
    post := multiset{};
    
    // Create a copy of m without one occurrence of p
    var remaining := m - multiset{p};
    
    // Partition the remaining elements
    var elements := remaining;
    while elements != multiset{}
        decreases |elements|
        invariant elements <= remaining
        invariant pre + post + elements + multiset{p} == m
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
    {
        var x :| x in elements;
        elements := elements - multiset{x};
        
        if x <= p {
            pre := pre + multiset{x};
        } else {
            post := post + multiset{x};
        }
    }
}