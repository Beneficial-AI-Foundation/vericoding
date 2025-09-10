predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    IsValidInteger(lines[0]) &&
    var t := ParseInt(lines[0]);
    t >= 0 && |lines| >= t + 1 &&
    (forall i :: 1 <= i <= t ==> (
        |SplitSpaces(lines[i])| >= 4 &&
        (forall j :: 0 <= j < 4 ==> IsValidInteger(SplitSpaces(lines[i])[j])) &&
        var parts := SplitSpaces(lines[i]);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);
        L >= 1 && v >= 1 && l >= 1 && r >= l && r <= L
    ))
}

predicate ValidOutput(output: string, input: string)
{
    forall c :: c in output ==> (c >= '0' && c <= '9') || c == '-' || c == '\n'
}

predicate OutputMatchesAlgorithm(output: string, input: string)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    t >= 0 &&
    var expectedLines := seq(t, i requires 0 <= i < t => 
        if i + 1 < |lines| && |SplitSpaces(lines[i + 1])| >= 4 then
            var parts := SplitSpaces(lines[i + 1]);
            var L := ParseInt(parts[0]);
            var v := ParseInt(parts[1]);
            var l := ParseInt(parts[2]);
            var r := ParseInt(parts[3]);
            var totalLanterns := L / v;
            var blockedLanterns := r / v - (l - 1) / v;
            var visibleLanterns := totalLanterns - blockedLanterns;
            IntToString(visibleLanterns)
        else
            "0"
    );
    output == JoinLines(expectedLines)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (
        (s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> s[i] >= '0' && s[i] <= '9') ||
        (s[0] != '-' && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9')
    )
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
    if s == "" then
        []
    else
        var lines: seq<string> := [];
        var i := 0;
        var start := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant 0 <= start <= i
            invariant forall x :: 0 <= x < |lines| ==> (
                lines[x] == s[var_SplitLines_start_at_index[x] .. var_SplitLines_end_at_index[x]] &&
                s[var_SplitLines_end_at_index[x]] == '\n'
            )
            ghost var var_SplitLines_start_at_index: seq<int>;
            ghost var var_SplitLines_end_at_index: seq<int>;
            fresh_seqs_len(var_SplitLines_start_at_index, var_SplitLines_end_at_index, |lines|)
        {
            if s[i] == '\n' {
                lines := lines + [s[start..i]];
                ghost var_SplitLines_start_at_index := var_SplitLines_start_at_index + [start];
                ghost var_SplitLines_end_at_index := var_SplitLines_end_at_index + [i];
                start := i + 1;
            }
            i := i + 1;
        }
        lines + [s[start..|s|]]
}

function SplitLinesAux(s: string, k: int): int
    requires k >= 0
    reads s
{
    if k == 0 then
        0
    else if k > 0 && exists i :: 0 <= i < |s| && s[i] == '\n' then
        var count := 0;
        var index := 0;
        while index < |s| && count < k
            invariant 0 <= index <= |s|
            invariant 0 <= count <= k
            invariant forall j :: 0 <= j < index ==> s[j] != '\n' || (count > 0 && exists l :: 0 <= l < j && s[l] == '\n' ) // This is not very precise
        {
            if s[index] == '\n' {
                count := count + 1;
            }
            index := index + 1;
        }
        if count == k then index else |s|
    else
        |s|
}

function SplitSpaces(s: string): seq<string>
{
    var parts: seq<string> := [];
    var i := 0;
    var start := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= i
        invariant forall k :: 0 <= k < |parts| ==> NoSpacesInside(parts[k])
        invariant forall k :: 0 <= k < |parts| ==> parts[k] == s[var_SplitSpaces_start_at_index[k] .. var_SplitSpaces_end_at_index[k]]
        ghost var var_SplitSpaces_start_at_index: seq<int>;
        ghost var var_SplitSpaces_end_at_index: seq<int>;
        fresh_seqs_len(var_SplitSpaces_start_at_index, var_SplitSpaces_end_at_index, |parts|)
    {
        if s[i] == ' ' {
            if i > start {
                parts := parts + [s[start..i]];
                ghost var_SplitSpaces_start_at_index := var_SplitSpaces_start_at_index + [start];
                ghost var_SplitSpaces_end_at_index := var_SplitSpaces_end_at_index + [i];
            }
            start := i + 1;
        }
        i := i + 1;
    }
    if i > start {
        parts := parts + [s[start..i]];
    }
    parts
}

predicate NoSpacesInside(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] != ' '
}

function ParseInt(s: string): int
    requires IsValidInteger(s)
{
    if s[0] == '-' then
        ParseIntPositive(s[1..]) * -1
    else
        ParseIntPositive(s)
}

function ParseIntPositive(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
    requires |s| > 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == (if i == 0 then 0 else StringToPartialInt_Proof(s[0..i]))
    {
        res := res * 10 + (s[i] - '0');
        i := i + 1;
    }
    res
}

function StringToPartialInt_Proof(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
    requires |s| > 0
{
    if |s| == 1 then
        s[0] - '0'
    else
        StringToPartialInt_Proof(s[0..|s|-1]) * 10 + (s[|s|-1] - '0')
}

function IntToString(n: int): string
    ensures IsValidInteger(IntToString(n))
{
    if n == 0 then
        "0"
    else if n < 0 then
        "-" + IntToStringPositive(-n)
    else
        IntToStringPositive(n)
}

function IntToStringPositive(n: int): string
    requires n >= 0
    ensures forall i :: 0 <= i < |IntToStringPositive(n)| ==> IntToStringPositive(n)[i] >= '0' && IntToStringPositive(n)[i] <= '9'
{
    if n == 0 then
        "0"
    else {
        var s := "";
        var temp_n := n;
        while temp_n > 0
            invariant temp_n >= 0
            invariant forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
        {
            s := char((temp_n % 10) + '0') + s;
            temp_n := temp_n / 10;
        }
        s
    }
}
function JoinLines(lines: seq<string>): string
{
    if |lines| == 0 then
        ""
    else if |lines| == 1 then
        lines[0]
    else
        lines[0] + "\n" + JoinLines(lines[1..])
}

ghost predicate fresh_seqs_len<T>(s1: seq<T>, s2: seq<T>, len: int)
{
  |s1| == len && |s2| == len
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures ValidOutput(output, input)
    ensures OutputMatchesAlgorithm(output, input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    var results: seq<string> := [];

    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |lines| >= t + 1 // t is parsed integer from lines[0], so lines has at least t+1 elements
        invariant (forall k :: 1 <= k <= t ==> 
            (
                |SplitSpaces(lines[k])| >= 4 &&
                (forall j :: 0 <= j < 4 ==> IsValidInteger(SplitSpaces(lines[k])[j]))
            )
        )
        invariant (forall k :: 0 <= k < i ==>
            var parts_k := SplitSpaces(lines[k+1]);
            var L_k := ParseInt(parts_k[0]);
            var v_k := ParseInt(parts_k[1]);
            var l_k := ParseInt(parts_k[2]);
            var r_k := ParseInt(parts_k[3]);
            var totalLanterns_k := L_k / v_k;
            var blockedLanterns_k := r_k / v_k - (l_k - 1) / v_k;
            var visibleLanterns_k := totalLanterns_k - blockedLanterns_k;
            results[k] == IntToString(visibleLanterns_k)
        )
        invariant ValidInput(input) // Added a loop invariant for ValidInput(input)
    {
        var currentProblem := lines[i + 1];
        var parts := SplitSpaces(currentProblem);
        var L := ParseInt(parts[0]);
        var v := ParseInt(parts[1]);
        var l := ParseInt(parts[2]);
        var r := ParseInt(parts[3]);

        var totalLanterns := L / v;
        var blockedLanterns := r / v - (l - 1) / v;
        var visibleLanterns := totalLanterns - blockedLanterns;

        results := results + [IntToString(visibleLanterns)];
        i := i + 1;
    }

    output := JoinLines(results);
    return output;
}
// </vc-code>

