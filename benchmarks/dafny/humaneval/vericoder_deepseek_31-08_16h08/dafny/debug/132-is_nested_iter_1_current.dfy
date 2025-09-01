

// <vc-helpers>
predicate nested_pair(s: seq<int>, x: int, y: int, z: int, w: int)
  requires 0 <= x < y < z < w < |s|
{
  s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
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
    invariant i >= 0
    invariant first_zero == -1 || 0 <= first_zero < i
    invariant second_zero == -1 || (first_zero != -1 && 0 <= second_zero < i)
    invariant first_one == -1 || (second_zero != -1 && 0 <= first_one < i)
    invariant second_one == -1 || (first_one != -1 && 0 <= second_one < i)
  {
    if s[i] == 0 {
      if first_zero == -1 {
        first_zero := i;
      } else if second_zero == -1 {
        second_zero := i;
      }
    } else if s[i] == 1 {
      if first_one == -1 {
        if second_zero != -1 {
          first_one := i;
        }
      } else if second_one == -1 {
        second_one := i;
      }
    }
    
    if second_zero != -1 && second_one != -1 {
      return true;
    }
    i := i + 1;
  }
  
  return false;
}
// </vc-code>

