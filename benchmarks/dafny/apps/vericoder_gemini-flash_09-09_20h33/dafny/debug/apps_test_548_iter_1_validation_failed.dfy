predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
lemma HasOddOrAllEven(a: seq<int>)
    ensures HasOdd(a) || AllEven(a)
{
    if !HasOdd(a) {
        // If there's no odd number, then all numbers must be even.
        // We can prove this by contradiction.
        // Assume there exists an i such that a[i] % 2 != 0.
        // Since a[i] % 2 is either 0 or 1 for integers, a[i] % 2 != 0 implies a[i] % 2 == 1.
        // This contradicts !HasOdd(a).
        // Therefore, forall i, a[i] % 2 == 0 must be true.
        // This means AllEven(a) holds.
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
    if HasOdd(a) {
        result := "First";
    } else if AllEven(a) {
        result := "Second";
    } else {
        // This case should ideally be unreachable given the properties of integers.
        // We know that an integer is either even or odd.
        // If the sequence does not have an odd number, then all its numbers must be even.
        // The helper lemma HasOddOrAllEven proves this.
        HasOddOrAllEven(a); // Invoke lemma to establish disjunction
        assert HasOdd(a) || AllEven(a);
        // If we reach here, it implies a logical impossibility given the properties of numbers.
        // Dafny verification will ensure this branch is never taken if the logic is sound.
        result := "Error"; // Fallback, though ideally unreachable for verification
    }
}
// </vc-code>

