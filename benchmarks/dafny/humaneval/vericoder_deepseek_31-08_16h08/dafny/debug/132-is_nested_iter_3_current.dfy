

// <vc-helpers>
predicate nested_pair(s: seq<int>, x: int, y: int, z: int, w: int)
  requires 0 <= x < y < z < w < |s|
{
  s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
}

lemma LemmaSequenceProperties(s: seq<int>, i: int, first_zero: int, second_zero: int, first_one: int, second_one: int)
  requires 0 <= i <= |s|
  requires first_zero >= -1 && second_zero >= -1 && first_one >= -1 && second_one >= -1
  requires first_zero != -1 ==> 0 <= first_zero < i
  requires second_zero != -1 ==> first_zero != -1 && 0 <= second_zero < i && first_zero < second_zero
  requires first_one != -1 ==> second_zero != -1 && 0 <= first_one < i && second_zero < first_one
  requires second_one != -1 ==> first_one != -1 && 0 <= second_one < i && first_one < second_one
  requires second_zero != -1 && second_one != -1 ==> 
    exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
{
  if second_zero != -1 && second_one != -1 {
    var x := first_zero;
    var y := second_zero;
    var z := first_one;
    var w := second_one;
    assert 0 <= x < y < z < w < |s|;
    assert s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1;
  }
}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var first_zero := -1;
  var second_zero := -1;
  var first_one := -1;
  var second_one := -1;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant first_zero == -1 || 0 <= first_zero < i
    invariant second_zero == -1 || (first_zero != -1 && 0 <= second_zero < i && first_zero < second_zero)
    invariant first_one == -1 || (second_zero != -1 && 0 <= first_one < i && second_zero < first_one)
    invariant second_one == -1 || (first_one != -1 && 0 <= second_one < i && first_one < second_one)
    invariant second_zero != -1 && second_one != -1 ==> 
      exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
  {
    if s[i] == 0 {
      if first_zero == -1 {
        first_zero := i;
      } else if second_zero == -1 && i > first_zero {
        second_zero := i;
      }
    } else if s[i] == 1 {
      if first_one == -1 {
        if second_zero != -1 {
          first_one := i;
        }
      } else if second_one == -1 && i > first_one {
        second_one := i;
      }
    }
    
    if second_zero != -1 && second_one != -1 {
      LemmaSequenceProperties(s, i+1, first_zero, second_zero, first_one, second_one);
      return true;
    }
    i := i + 1;
  }
  
  if second_zero != -1 && second_one != -1 {
    LemmaSequenceProperties(s, |s|, first_zero, second_zero, first_one, second_one);
    return true;
  }
  return false;
}
// </vc-code>

