

// <vc-helpers>
lemma SetComprehensionInduction(s: seq<int>, k: nat)
  requires 0 <= k <= |s|
  ensures |set i | 0 <= i < k && digits_sum(s[i]) > 0| == CountPositiveDigitSums(s, k)
{
  if k == 0 {
    assert set i | 0 <= i < 0 && digits_sum(s[i]) > 0 == {};
  } else {
    SetComprehensionInduction(s, k - 1);
    var prev_set := set i | 0 <= i < k - 1 && digits_sum(s[i]) > 0;
    var curr_set := set i | 0 <= i < k && digits_sum(s[i]) > 0;
    
    if digits_sum(s[k - 1]) > 0 {
      assert curr_set == prev_set + {k - 1};
    } else {
      assert curr_set == prev_set;
    }
  }
}

function CountPositiveDigitSums(s: seq<int>, k: nat): nat
  requires k <= |s|
{
  if k == 0 then 0
  else if digits_sum(s[k - 1]) > 0 then 1 + CountPositiveDigitSums(s, k - 1)
  else CountPositiveDigitSums(s, k - 1)
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
    assert set j | 0 <= j < i + 1 && digits_sum(s[j]) > 0 == 
           (set j | 0 <= j < i && digits_sum(s[j]) > 0) + 
           (if digits_sum(s[i]) > 0 then {i} else {});
    
    if digits_sum(s[i]) > 0 {
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