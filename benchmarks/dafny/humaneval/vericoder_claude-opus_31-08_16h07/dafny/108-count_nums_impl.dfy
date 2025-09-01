

// <vc-helpers>
lemma SetCardinalityAdd<T>(s: set<T>, x: T)
  ensures x in s ==> |s| == |s - {x}| + 1
  ensures x !in s ==> |s + {x}| == |s| + 1
{
}

lemma SetComprehensionStep(s: seq<int>, i: nat)
  requires 0 <= i < |s|
  ensures (set j | 0 <= j < i + 1 && digits_sum(s[j]) > 0) ==
          (set j | 0 <= j < i && digits_sum(s[j]) > 0) + 
          (if digits_sum(s[i]) > 0 then {i} else {})
{
  var prev_set := set j | 0 <= j < i && digits_sum(s[j]) > 0;
  var curr_set := set j | 0 <= j < i + 1 && digits_sum(s[j]) > 0;
  
  if digits_sum(s[i]) > 0 {
    assert i !in prev_set;
    assert curr_set == prev_set + {i};
  } else {
    assert i !in curr_set;
    assert curr_set == prev_set;
  }
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && digits_sum(s[j]) > 0|
  {
    var prev_set := set j | 0 <= j < i && digits_sum(s[j]) > 0;
    SetComprehensionStep(s, i);
    
    if digits_sum(s[i]) > 0 {
      SetCardinalityAdd(prev_set, i);
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end