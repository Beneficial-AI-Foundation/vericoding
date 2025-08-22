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
    var c0 := a[0];
    var c1 := a[1];
    var c2 := a[2];
    
    /* code modified by LLM (iteration 4): Fixed string construction using sequence constructor syntax */
    if c0 <= c1 && c1 <= c2 {
        b := seq(3, i => if i == 0 then c0 else if i == 1 then c1 else c2);
    } else if c0 <= c2 && c2 <= c1 {
        b := seq(3, i => if i == 0 then c0 else if i == 1 then c2 else c1);
    } else if c1 <= c0 && c0 <= c2 {
        b := seq(3, i => if i == 0 then c1 else if i == 1 then c0 else c2);
    } else if c1 <= c2 && c2 <= c0 {
        b := seq(3, i => if i == 0 then c1 else if i == 1 then c2 else c0);
    } else if c2 <= c0 && c0 <= c1 {
        b := seq(3, i => if i == 0 then c2 else if i == 1 then c0 else c1);
    } else {
        b := seq(3, i => if i == 0 then c2 else if i == 1 then c1 else c0);
    }
}