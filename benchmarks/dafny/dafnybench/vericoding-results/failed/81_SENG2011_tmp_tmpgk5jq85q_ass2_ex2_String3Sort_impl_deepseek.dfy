// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

// <vc-helpers>
lemma SwapSorted(a: string, i: int, j: int) returns (b: string)
  requires |a| == 3
  requires 0 <= i < |a| && 0 <= j < |a|
  ensures |a| == |b|
  ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
{
  var arr0 := a[0];
  var arr1 := a[1];
  var arr2 := a[2];
  var temp: char;
  
  if i == 0 { temp := arr0; }
  else if i == 1 { temp := arr1; }
  else { temp := arr2; }
  
  if i == 0 {
    if j == 0 { arr0 := temp; }
    else if j == 1 { arr0 := arr1; }
    else { arr0 := arr2; }
  } else if i == 1 {
    if j == 0 { arr1 := arr0; }
    else if j == 1 { arr1 := temp; }
    else { arr1 := arr2; }
  } else {
    if j == 0 { arr2 := arr0; }
    else if j == 1 { arr2 := arr1; }
    else { arr2 := temp; }
  }
  
  if j == 0 { arr0 := temp; }
  else if j == 1 { arr1 := temp; }
  else { arr2 := temp; }
  
  b := [arr0, arr1, arr2];
  assert |b| == 3;
}

ghost method SortThreeSorted(a: string) returns (b: string)
  requires |a| == 3
  ensures Sorted(b, 0, |b|)
  ensures |a| == |b|
  ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
{
  var c0 := a[0];
  var c1 := a[1];
  var c2 := a[2];
  
  if c0 > c1 {
    var temp := c0;
    c0 := c1;
    c1 := temp;
  }
  if c1 > c2 {
    var temp := c1;
    c1 := c2;
    c2 := temp;
  }
  if c0 > c1 {
    var temp := c0;
    c0 := c1;
    c1 := temp;
  }
  
  b := [c0, c1, c2];
  assert |b| == 3;
  assert Sorted(b, 0, 3) by {
    forall j: int, k: int | 0 <= j < k < 3 {
      if j == 0 && k == 1 { assert b[j] == c0 <= c1 == b[k]; }
      if j == 0 && k == 2 { assert b[j] == c0 <= c2 == b[k]; }
      if j == 1 && k == 2 { assert b[j] == c1 <= c2 == b[k]; }
    }
  }
  assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]} by {
    assert multiset{b[0], b[1], b[2]} == multiset{c0, c1, c2};
    assert multiset{a[0], a[1], a[2]} == multiset{c0, c1, c2};
  }
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
  
  if c0 > c1 {
    var temp := c0;
    c0 := c1;
    c1 := temp;
  }
  if c1 > c2 {
    var temp := c1;
    c1 := c2;
    c2 := temp;
  }
  if c0 > c1 {
    var temp := c0;
    c0 := c1;
    c1 := temp;
  }
  
  b := [c0, c1, c2];
}
// </vc-code>

