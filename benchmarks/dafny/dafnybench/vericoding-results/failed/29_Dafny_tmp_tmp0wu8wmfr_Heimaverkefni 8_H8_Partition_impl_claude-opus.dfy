// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

// <vc-helpers>
// Helper to find the minimum element in a non-empty multiset
function MinOfMultiset(m: multiset<int>): int
    requires |m| > 0
    ensures MinOfMultiset(m) in m
    ensures forall x | x in m :: MinOfMultiset(m) <= x
{
    var elem :| elem in m;
    if |m| == 1 then
        elem
    else if forall x | x in m && x != elem :: elem <= x then
        elem
    else
        var rest := m - multiset{elem};
        if |rest| == 0 then
            elem
        else
            var minRest := MinOfMultiset(rest);
            if elem <= minRest then elem else minRest
}

// Helper function to convert multiset to set
function SetFromMultiset(m: multiset<int>): set<int>
    requires |m| > 0
    ensures |SetFromMultiset(m)| > 0
    ensures forall x :: x in SetFromMultiset(m) <==> x in m
    ensures |SetFromMultiset(m)| <= |m|
{
    set x | x in m
}

// Helper function to deterministically pick an element from a set
function PickFromSet(s: set<int>): int
    requires |s| > 0
    ensures PickFromSet(s) in s
{
    var x :| x in s; x
}

// Helper method to get minimum (compilable version)
method GetMin(m: multiset<int>) returns (min: int)
    requires |m| > 0
    ensures min in m
    ensures forall x | x in m :: min <= x
{
    var remaining := m;
    min :| min in remaining;
    
    while |remaining| > 1
        invariant |remaining| > 0
        invariant remaining <= m
        invariant min in m
        invariant forall x | x in (m - remaining) :: min <= x
        invariant exists y | y in remaining :: 
            (forall x | x in remaining :: y <= x) && 
            (forall x | x in m :: y <= x || x in remaining)
        decreases |remaining|
    {
        var next :| next in remaining;
        
        if next < min {
            min := next;
        }
        remaining := remaining - multiset{next};
    }
}

// Helper method to pick an element from a set (compilable)
method PickElement(s: set<int>) returns (elem: int)
    requires |s| > 0
    ensures elem in s
{
    elem :| elem in s;
}
// </vc-helpers>

// <vc-spec>
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// <vc-code>
{
    p := GetMin(m);
    var remaining := m - multiset{p};
    
    pre := multiset{};
    post := multiset{};
    
    while remaining != multiset{}
        invariant p in m
        invariant m == pre + multiset{p} + post + remaining
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
        invariant |remaining| >= 0
        decreases |remaining|
    {
        if |remaining| > 0 {
            var elem :| elem in remaining;
            
            if elem <= p {
                pre := pre + multiset{elem};
            } else {
                post := post + multiset{elem};
            }
            remaining := remaining - multiset{elem};
        }
    }
}
// </vc-code>

