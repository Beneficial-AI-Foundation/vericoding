predicate strictNegative(v:array<int>,i:int,j:int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isPermutation(s:seq<int>, t:seq<int>)
{multiset(s)==multiset(t)}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
// </vc-spec>
// <vc-code>
{
  var left := 0;
  var right := v.Length - 1;
  while left <= right
    invariant 0 <= left <= right + 1 <= v.Length
    invariant positive(v[0..left])
    invariant strictNegative(v, right + 1, v.Length)
    invariant multiset(v[0..v.Length]) == multiset(old(v[0..v.Length]))
  {
    if v[left] >= 0 {
      left := left + 1;
    } else if v[right] < 0 {
      right := right - 1;
    } else {
      var temp := v[left];
      v[left] := v[right];
      v[right] := temp;
      left := left + 1;
      right := right - 1;
    }
  }
  i := left;
}
// </vc-code>

