// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
lemma SortedThreeElements(s: string)
requires |s| == 3
requires s[0] <= s[1] <= s[2]
ensures Sorted(s, 0, 3)
{
    forall j, k | 0 <= j < k < 3 ensures s[j] <= s[k] {
        if j == 0 && k == 1 {
            assert s[j] <= s[k];
        } else if j == 0 && k == 2 {
            assert s[0] <= s[1] <= s[2];
        } else if j == 1 && k == 2 {
            assert s[j] <= s[k];
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var c0 := a[0];
    var c1 := a[1];
    var c2 := a[2];
    
    if c0 <= c1 <= c2 {
        b := [c0, c1, c2];
    } else if c0 <= c2 <= c1 {
        b := [c0, c2, c1];
    } else if c1 <= c0 <= c2 {
        b := [c1, c0, c2];
    } else if c1 <= c2 <= c0 {
        b := [c1, c2, c0];
    } else if c2 <= c0 <= c1 {
        b := [c2, c0, c1];
    } else {
        b := [c2, c1, c0];
    }
    
    SortedThreeElements(b);
}
// </vc-code>
