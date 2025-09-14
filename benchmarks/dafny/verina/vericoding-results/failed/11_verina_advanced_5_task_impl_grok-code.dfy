// <vc-preamble>
function ListToNat(l: seq<nat>): nat
    decreases |l|
{
    if |l| == 0 then
        0
    else
        l[0] + 10 * ListToNat(l[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to prove list and nat conversion inverse */
function NatToList(num: nat): seq<nat>
{
    var temp := if num == 0 then [] else [num % 10] + NatToList(num / 10);
    if |temp| == 0 then [0] else temp
}

lemma ListToNatNatToListInverse(n: nat)
    ensures ListToNat(NatToList(n)) == n
{
  if n != 0 {
    ListToNatNatToListInverse(n / 10);
  }
}
// </vc-helpers>

// <vc-spec>
method AddTwoNumbers(l1: array<nat>, l2: array<nat>) returns (result: array<nat>)
    requires 
        l1.Length > 0 &&
        l2.Length > 0 &&
        (forall i :: 0 <= i < l1.Length ==> l1[i] < 10) &&
        (forall i :: 0 <= i < l2.Length ==> l2[i] < 10) &&
        (l1[l1.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0)) &&
        (l2[l2.Length - 1] != 0 || (l2.Length == 1 && l2[0] == 0))
    ensures
        result.Length > 0 &&
        ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]) &&
        (forall i :: 0 <= i < result.Length ==> result[i] < 10) &&
        (result[result.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0 && l2.Length == 1 && l2[0] == 0 && result.Length == 1 && result[0] == 0))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implemented addition using list-to-nat conversion and back */
  var num1 := ListToNat(l1[..]);
  var num2 := ListToNat(l2[..]);
  var sum := num1 + num2;
  var digits := NatToList(sum);
  result := new nat[|digits|];
  for i := 0 to |digits| - 1 {
    result[i] := digits[i];
  }
  ListToNatNatToListInverse(sum);
}
// </vc-code>
