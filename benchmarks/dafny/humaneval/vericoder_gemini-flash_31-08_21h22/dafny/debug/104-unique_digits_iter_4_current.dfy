function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
function DigitsOf(n: int): set<int>
  requires n >= 0
  decreases n
{
  if n == 0 then {0} else {n % 10} + DigitsOf(n / 10)
}

function IsUniqueDigit(n: int): bool
  requires n >= 0
{
  var s := DigitsOf(n);
  |s| <= 1
}

lemma lemma_HasNoEvenDigit_preserves_unique_digit_property(k: int)
  requires k >= 0
  ensures HasNoEvenDigit(k) ==> (forall d | d in DigitsOf(k) :: d % 2 == 1)
{
  if k < 10 {
    // If k < 10, DigitsOf(k) is just {k}. The property is trivial.
  } else {
    // Inductive step:
    // If k has no even digits, then k%10 has no even digits and k/10 has no even digits.
    // The digits of k are the union of the digits of k%10 and k/10.
    // If all digits in k%10 and k/10 satisfy the property, then all digits in k satisfy it.
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var unique_has_no_even_digits: seq<int> := [];
    for i := 0 to |x| - 1
        invariant forall k :: 0 <= k < |unique_has_no_even_digits| ==> HasNoEvenDigit(unique_has_no_even_digits[k])
        invariant forall e :: e in unique_has_no_even_digits ==> (e in x[..i] && HasNoEvenDigit(e))
        invariant forall e :: (e in x[..i] && HasNoEvenDigit(e)) ==> (e in unique_has_no_even_digits)
    {
        if HasNoEvenDigit(x[i]) {
            var found := false;
            for j := 0 to |unique_has_no_even_digits| - 1
                invariant forall k :: 0 <= k < j ==> unique_has_no_even_digits[k] != x[i]
            {
                if unique_has_no_even_digits[j] == x[i] {
                    found := true;
                    break;
                }
            }
            if !found {
                unique_has_no_even_digits := unique_has_no_even_digits + [x[i]];
            }
        }
    }

    // Sort the sequence using Selection Sort
    if |unique_has_no_even_digits| > 1 { // Only sort if there's more than one element
        for i := 0 to |unique_has_no_even_digits| - 2
            invariant forall k :: 0 <= k < i ==> forall l :: k < l < |unique_has_no_even_digits| ==> unique_has_no_even_digits[k] <= unique_has_no_even_digits[l]
            invariant forall k :: 0 <= k < |unique_has_no_even_digits| ==> HasNoEvenDigit(unique_has_no_even_digits[k])
            invariant forall e :: e in unique_has_no_even_digits ==> e in x
            invariant multiset(unique_has_no_even_digits) == multiset(old(unique_has_no_even_digits))
        {
            var min_idx := i;
            for j := i + 1 to |unique_has_no_even_digits| - 1
                invariant i <= min_idx < j
                invariant forall k :: i <= k < j ==> unique_has_no_even_digits[min_idx] <= unique_has_no_even_digits[k]
                invariant min_idx >= i
            {
                if unique_has_no_even_digits[j] < unique_has_no_even_digits[min_idx] {
                    min_idx := j;
                }
            }
            // Swap elements only if min_idx is different from i
            if min_idx != i {
                var temp := unique_has_no_even_digits[i];
                unique_has_no_even_digits := unique_has_no_even_digits[..i] + [unique_has_no_even_digits[min_idx]] + unique_has_no_even_digits[i+1 .. min_idx] + [temp] + unique_has_no_even_digits[min_idx+1 ..];
            }
        }
    }

    result := unique_has_no_even_digits;
}
// </vc-code>

