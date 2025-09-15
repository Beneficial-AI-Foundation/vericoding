// <vc-preamble>
function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): step function representing contribution of a single symbol */
function step(x: int): int { if x == 0 then 1 else -1 }
/* helper modified by LLM (iteration 2): lemma to extend CalcBal forward by one position */
lemma CalcBalExtend(s: seq<int>, i: int, j: int, acc: int)
  requires 0 <= i <= j < |s|
  ensures CalcBal(s, i, j + 1, acc) == (if s[j] == 0 then 1 else -1) + CalcBal(s, i, j, acc)
{
}

// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 

    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1

    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute b via universal properties and provide explicit existential witnesses when they fail */
  var A := (forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0);
  var B := (forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0);
  b := A && B;
  if !b {
    if !A {
      assert exists i :: 0 <= i <= |s1| && !(CalcBal(s1, 0, i, 0) >= 0);
      assert exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0;
    } else {
      assert !B;
      assert exists i :: 0 <= i <= |s2| && !(CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0);
      assert exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0;
    }
  }
}
// </vc-code>
