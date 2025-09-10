function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
function IsPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
    if |s| % k != 0 {
        return "NO";
    } else {
        var segmentLength := |s| / k;
        var allSegmentsArePalindromes := true;
        for i := 0 to k - 1
            invariant 0 <= i <= k
            invariant allSegmentsArePalindromes == (forall j :: 0 <= j < i ==> IsPalindrome(s[j * segmentLength .. (j + 1) * segmentLength]))
            invariant k > 0
            invariant forall x :: 0 <= x < i ==> isPalindrome(s[x * segmentLength .. (x + 1) * segmentLength])
            decreases k - i
        {
            var segment := s[i * segmentLength .. (i + 1) * segmentLength];
             if !IsPalindrome(segment) {
                allSegmentsArePalindromes := false;
                break;
            }
        }

        if allSegmentsArePalindromes {
            return "YES";
        } else {
            return "NO";
        }
    }
}
// </vc-code>

