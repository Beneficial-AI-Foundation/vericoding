//ATOM
// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
  forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

//IMPL String3Sort
method String3Sort(a: string) returns (b: string) 
requires |a| == 3
ensures Sorted(b, 0, |b|)
ensures |a| == |b|
ensures multiset(a[..]) == multiset(b[..])
{
    var c0, c1, c2 := a[0], a[1], a[2];
    
    /* code modified by LLM (iteration 2): fixed string construction to use proper string literals instead of sequence literals */
    // Sort the three characters
    if c0 <= c1 <= c2 {
        b := [c0] + [c1] + [c2];
    } else if c0 <= c2 <= c1 {
        b := [c0] + [c2] + [c1];
    } else if c1 <= c0 <= c2 {
        b := [c1] + [c0] + [c2];
    } else if c1 <= c2 <= c0 {
        b := [c1] + [c2] + [c0];
    } else if c2 <= c0 <= c1 {
        b := [c2] + [c0] + [c1];
    } else {
        b := [c2] + [c1] + [c0];
    }
    
    /* code modified by LLM (iteration 2): added lemma to help Dafny verify multiset preservation for strings */
    assert a[..] == [c0, c1, c2];
}