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
function Pow10(n: nat): nat {
	if n == 0 then 1
	else 10 * Pow10(n - 1)
}
 /* helper modified by LLM (iteration 3): Added Pow10 function for loop invariants to prove liste ajouta tion correctness. */
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
/* code modified by LLM (iteration 4): Updated loop invariant to correctly accumulate the sum value with carry and remaining parts of l1 and l2 sequences. */
{
	var maxl: nat := if l1.Length > l2.Length then l1.Length else l2.Length;
	var res: seq<nat> := [];
	var carry: nat := 0;
	var i: nat := 0;
	while i < maxl
		decreases maxl - i
		invariant 0 <= i <= maxl
		invariant |res| == i
		invariant 0 <= carry <= 2
		invariant forall k :: 0 <= k < |res| ==> res[k] < 10
		invariant ListToNat(res) + carry * Pow10(i) + ListToNat(l1[i..]) + ListToNat(l2[i..]) == ListToNat(l1[..]) + ListToNat(l2[..])
	{
		var a: nat := if i < l1.Length then l1[i] else 0;
		var b: nat := if i < l2.Length then l2[i] else 0;
		var data: nat := a + b + carry;
		carry := data / 10;
		res := res + [data % 10];
		i := i + 1;
	}
	if carry > 0 {
		res := res + [carry];
	}
	assert |res| > 0;
	result := new nat[|res|];
	for j := 0 to |res| - 1
		invariant j <= |res|
		invariant forall k :: 0 <= k < j ==> result[k] == res[k]
	{
		result[j] := res[j];
	}
}
// </vc-code>
