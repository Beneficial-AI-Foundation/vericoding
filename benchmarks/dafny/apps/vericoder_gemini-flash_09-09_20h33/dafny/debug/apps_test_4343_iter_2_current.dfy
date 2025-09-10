function median_string(s: string, t: string, k: int): string
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
{
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    var median_val := (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}

function string_to_base26(s: string): nat
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
{
    if |s| == 0 then 0
    else (s[0] as int - 'a' as int) * pow26(|s| - 1) + string_to_base26(s[1..])
}

function base26_to_string(val: nat, k: int): string
    requires k >= 1
    ensures |base26_to_string(val, k)| == k
    ensures forall i :: 0 <= i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z'
{
    if k == 1 then [((val % 26) + ('a' as int)) as char]
    else base26_to_string(val / 26, k - 1) + [((val % 26) + ('a' as int)) as char]
}

function pow26(n: nat): nat
{
    if n == 0 then 1 else 26 * pow26(n - 1)
}

// <vc-helpers>
// Define the power function for base 26
function pow26(n: nat): nat
{
    if n == 0 then 1 else 26 * pow26(n - 1)
}

// Convert a string to its base 26 integer representation
function string_to_base26(s: string): nat
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
    decreases |s|
{
    if |s| == 0 then 0
    else (s[0] as int - 'a' as int) * pow26(|s| - 1) + string_to_base26(s[1..])
}

// Convert a base 26 integer to a string of length k
function base26_to_string(val: nat, k: int): string
    requires k >= 1
    // The maximum possible value for a string of length k
    requires val <= 26 * pow26(k) - 1 // this means val can be fully represented by k characters
    ensures |base26_to_string(val, k)| == k
    ensures forall i :: 0 <= i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z'
    decreases k
{
    if k == 1 then [((val % 26) + ('a' as int)) as char]
    else base26_to_string(val / 26, k - 1) + [((val % 26) + ('a' as int)) as char]
}

// Helper function to calculate the median string value
function median_string(s: string, t: string, k: int): string
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    var median_val := (s_val + t_val) / 2;
    // Prove that median_val is within the representable range for base26_to_string
    // The maximum value for a k-length string is 26^k - 1 (all 'z's).
    // s_val and t_val are at most 26^k - 1.
    // So (s_val + t_val) / 2 is at most (2 * (26^k - 1)) / 2 = 26^k - 1.
    // This satisfies the precondition val <= 26 * pow26(k) - 1 for base26_to_string.
    ensures s_val <= median_val <= t_val
{
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    var median_val := (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, s: string, t: string) returns (result: string)
    requires k >= 1
    requires |s| == k
    requires |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures |result| == k
    ensures forall i :: 0 <= i < k ==> 'a' <= result[i] <= 'z'
    ensures s <= result <= t
    ensures result == median_string(s, t, k)
// </vc-spec>
// <vc-code>
{
    result := median_string(s, t, k);
}
// </vc-code>

