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
/* helper modified by LLM (iteration 5): Fixed compilation error with function return by explicitly using `returns` keyword. */
function AddDigits(digit1: nat, digit2: nat, carry: nat) returns (sum_digit: nat, new_carry: nat)
    requires digit1 < 10 && digit2 < 10 && carry < 2
    ensures sum_digit < 10 && new_carry < 2
{
    var sum := digit1 + digit2 + carry;
    var sum_digit_val := sum % 10;
    var new_carry_val := sum / 10;
    return (sum_digit_val, new_carry_val);
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
/* code modified by LLM (iteration 5): The previous iteration had parse errors in the helper function. This iteration fixes those parse errors in the helper function but keeps the main logic as is for now. */
{
    var list1 := l1[..];
    var list2 := l2[..];
    var n1 := |list1|;
    var n2 := |list2|;

    var maxLength := if n1 > n2 then n1 else n2;
    var currentResult := new nat[maxLength + 1];
    var i := 0;
    var carry := 0;

    while i < maxLength
        invariant 0 <= i <= maxLength
        invariant carry < 2
        invariant forall k :: 0 <= k < i ==> currentResult[k] < 10
        // invariant ListToNat(currentResult[..i]) == ListToNat(list1[n1-i..n1]) + ListToNat(list2[n2-i..n2]) + carry * (10 `pow` i)
        decreases maxLength - i
    {
        var digit1 := if i < n1 then list1[n1 - 1 - i] else 0;
        var digit2 := if i < n2 then list2[n2 - 1 - i] else 0;
        var sum_digit: nat;
        var new_carry: nat;

        sum_digit, new_carry := AddDigits(digit1, digit2, carry);

        currentResult[i] := sum_digit;
        carry := new_carry;
        i := i + 1;
    }

    if carry == 0 {
        result := new nat[maxLength];
        i := 0;
        while i < maxLength
            invariant 0 <= i <= maxLength
            invariant forall k :: 0 <= k < i ==> result[k] < 10
            invariant forall k :: 0 <= k < i ==> result[k] == currentResult[maxLength - 1 - k]
            decreases maxLength - i
        {
            result[i] := currentResult[maxLength - 1 - i];
            i := i + 1;
        }
    } else {
        result := new nat[maxLength + 1];
        result[0] := carry;
        i := 0;
        while i < maxLength
            invariant 0 <= i <= maxLength
            invariant result[0] == carry
            invariant forall k :: 1 <= k <= i ==> result[k] < 10
            invariant forall k :: 1 <= k <= i ==> result[k] == currentResult[maxLength - k]
            decreases maxLength - i
        {
            result[i + 1] := currentResult[maxLength - 1 - i];
            i := i + 1;
        }
    }
}
// </vc-code>
