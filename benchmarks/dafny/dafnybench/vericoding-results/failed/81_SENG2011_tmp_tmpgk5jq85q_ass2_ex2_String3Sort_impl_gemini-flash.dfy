// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
function charValue(c: char): int
{
  c as int
}

// Helper to prove sorted property for a fixed 3-element string
lemma CharArray3Sorted(c0: char, c1: char, c2: char)
  returns (b: string)
  ensures b[0] == c0 && b[1] == c1 && b[2] == c2
  ensures Sorted(b, 0, |b|)
  ensures |b| == 3
{
  var arr := new char[](c0, c1, c2);
  b := new string(arr);
}
// </vc-helpers>

// <vc-spec>
method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
// </vc-spec>
// <vc-code>
{
    var c0 := a[0];
    var c1 := a[1];
    var c2 := a[2];

    if charValue(c0) > charValue(c1) {
        var temp := c0;
        c0 := c1;
        c1 := temp;
    }

    if charValue(c1) > charValue(c2) {
        var temp := c1;
        c1 := c2;
        c2 := temp;
    }

    if charValue(c0) > charValue(c1) {
        var temp := c0;
        c0 := c1;
        c1 := temp;
    }
    
    var arr := new char[](c0, c1, c2);
    b := new string(arr);
    assert charValue(c0) <= charValue(c1);
    assert charValue(c1) <= charValue(c2);
    assert Sorted(b, 0, |b|);
}
// </vc-code>

