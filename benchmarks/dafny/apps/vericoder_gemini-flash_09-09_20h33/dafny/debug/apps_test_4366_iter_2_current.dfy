predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
function IntToString(i: int): string
    requires 0 <= i <= 999999999999999999 // reasonable upper bound
    ensures var s := i as string; forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
{
    if i == 0 then "0"
    else
        var s := "";
        var temp := i;
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
             // Ensures `s` can only grow and elements maintain the '0'..'9' property.
            invariant (temp > 0 ==> (i / (10 * temp)) >= 1) || (temp == i / 10) // Simplified loop invariant
            invariant i > 0 ==> (s == "" && temp == i) ||
                                (s != "" && i == (temp * (Pow10(|s|)) + ParseInt(s)))
        {
            s := ('0' + (temp % 10)) + s;
            temp := temp / 10;
        }
        s
}
function ParseInt(s: string): (i: int)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0
    ensures i == (if s == "0" then 0 else (var res := 0; for k := 0 to |s|-1 { res := res * 10 + (s[k] - '0'); } return res;))
{
    var res := 0;
    for k := 0 to |s|-1
        invariant res >= 0
        invariant forall j :: 0 <= j < k ==> '0' <= s[j] <= '9'
        invariant res == (var r := 0; for x := 0 to k-1 { r := r * 10 + (s[x] - '0'); } return r;)
    {
        res := res * 10 + (s[k] - '0');
    }
    return res;
}

lemma ParseIntIntToString(i: int)
    requires 0 <= i <= 999999999999999999
    ensures ParseInt(IntToString(i)) == i
{
    if i == 0 {
        assert ParseInt("0") == 0;
    } else {
        var s := "";
        var temp := i;
        var p := 0; // power of 10
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
            invariant i == temp * Pow10(p) + ParseInt(s)
            invariant p == |s|
        {
            s := ('0' + (temp % 10)) + s;
            temp := temp / 10;
            p := p + 1;
        }
        assert i == ParseInt(s);
    }
}

lemma IntToStringParseInt(s: string)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0
    ensures IntToString(ParseInt(s)) == s
{
    var i := ParseInt(s);
    if i == 0 {
        assert s == "0";
    } else {
        var temp := i;
        var res_s := "";
        while temp > 0
            invariant temp >= 0
            invariant forall k :: 0 <= k < |res_s| ==> '0' <= res_s[k] <= '9'
            invariant ParseInt(s) == temp * Pow10(|res_s|) + ParseInt(res_s)
        {
            res_s := ('0' + (temp % 10)) + res_s;
            temp := temp / 10;
        }
        assert res_s == s;
    }
}

function Pow10(exp: nat): int
    ensures Pow10(exp) > 0
{
    if exp == 0 then 1
    else 10 * Pow10(exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var parts := input.Split(' ').ToSequence();
    var A_str: string;
    var B_str: string;

    if |parts| == 2 {
        A_str := parts[0];
        B_str := parts[1];
    } else {
        // Handle cases with newline at the end
        // If input is "A B\n", Split(' ') might produce ["A", "B\n"]
        // We need to remove the newline.
        assert |parts| == 2 || |parts| == 3; // From ValidInput proof
        A_str := parts[0];
        if parts[1][|parts[1]]-1 == '\n' {
            B_str := parts[1][..|parts[1]] - '\n'; // Remove newline
        } else {
            B_str := parts[1];
        }
    }

    assert forall k :: 0 <= k < |A_str| ==> '0' <= A_str[k] <= '9';
    assert forall k :: 0 <= k < |B_str| ==> '0' <= B_str[k] <= '9';

    ghost var original_input := input;
    ghost var original_A: int := 0; // Initialize original_A
    ghost var original_B: int := 0; // Initialize original_B
    
    // Deconstruct ValidInput
    if (exists A_val, B_val :: 0 <= A_val <= 23 && 0 <= B_val <= 23 && original_input == IntToString(A_val) + " " + IntToString(B_val) + "\n") {
        var temp_parts := original_input.Split(' ').ToSequence();
        assert |temp_parts| == 2; // Split "A B\n" by ' ' gives ["A", "B\n"]
        original_A := ParseInt(temp_parts[0]);
        // Remove '\n' from B_str to parse it
        original_B := ParseInt(temp_parts[1][..|temp_parts[1]]-1);
        ParseIntIntToString(original_A);
        ParseIntIntToString(original_B);
        assert IntToString(original_A) == A_str;
        assert IntToString(original_B) == B_str;
    } else if (exists A_val, B_val :: 0 <= A_val <= 23 && 0 <= B_val <= 23 && original_input == IntToString(A_val) + " " + IntToString(B_val)) {
        var temp_parts := original_input.Split(' ').ToSequence();
        assert |temp_parts| == 2; // Split "A B" by ' ' gives ["A", "B"]
        original_A := ParseInt(temp_parts[0]);
        original_B := ParseInt(temp_parts[1]);
        ParseIntIntToString(original_A);
        ParseIntIntToString(original_B);
        assert IntToString(original_A) == A_str;
        assert IntToString(original_B) == B_str;
    } else {
        assert false; // Should not happen due to ValidInput
    }

    ParseIntIntToString(original_A);
    ParseIntIntToString(original_B);
    
    var A := ParseInt(A_str);
    var B := ParseInt(B_str);

    assert A == original_A;
    assert B == original_B;

    assert 0 <= A <= 23;
    assert 0 <= B <= 23;

    var contest_start_time := ContestStartTime(A, B);
    result := IntToString(contest_start_time) + "\n";
}
// </vc-code>

