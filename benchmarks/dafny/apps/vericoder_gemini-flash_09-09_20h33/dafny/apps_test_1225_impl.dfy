predicate ValidInput(h: int) {
    h >= 1
}

function ComputeAttacks(h: int): int
    requires h >= 0
    ensures h == 0 ==> ComputeAttacks(h) == 0
    ensures h > 0 ==> ComputeAttacks(h) > 0
{
    ComputeAttacksIterative(h, 0)
}

function ComputeAttacksIterative(h: int, n: int): int
    requires h >= 0 && n >= 0
    ensures h == 0 ==> ComputeAttacksIterative(h, n) == 0
    ensures h > 0 ==> ComputeAttacksIterative(h, n) > 0
{
    if h == 0 then 0
    else pow2(n) + ComputeAttacksIterative(h / 2, n + 1)
}

function pow2(n: int) : int
    requires n >= 0
    ensures pow2(n) >= 1
    ensures pow2(n) == if n == 0 then 1 else 2 * pow2(n-1)
{
    if n <= 0 then 1
    else 2 * pow2(n-1)
}

function ParseIntFunc(s: string): int
    requires |s| > 0
    ensures ParseIntFunc(s) >= 0
{
    ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseIntHelper(s, i, acc) >= 0
    decreases |s| - i
{
    if i >= |s| || s[i] == '\n' || s[i] == ' ' then acc
    else if '0' <= s[i] <= '9' then
        ParseIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelper(s, i + 1, acc)
}

function IntToStringFunc(n: int): string
    requires n >= 0
    ensures |IntToStringFunc(n)| > 0
    ensures n == 0 ==> IntToStringFunc(n) == "0"
    ensures n > 0 ==> |IntToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n >= 0
    ensures |IntToStringHelper(n, acc)| >= |acc|
    decreases n
{
    if n == 0 then acc
    else
        var digit := n % 10;
        var digitChar := ('0' as int + digit) as char;
        IntToStringHelper(n / 10, [digitChar] + acc)
}

// <vc-helpers>
function IsDigit(c: char): bool {
    '0' <= c <= '9'
}

function ParseIntHelperCorrect(s: string, i: int, acc: int): (res: int)
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures res >= 0
    decreases |s| - i
{
    if i >= |s| then acc
    else if s[i] == '\n' || s[i] == ' ' then acc
    else if IsDigit(s[i]) then
        ParseIntHelperCorrect(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        ParseIntHelperCorrect(s, i + 1, acc)
}

lemma {:induction acc} ParseIntHelperEquivalent(s: string, i: int, acc: int)
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseIntHelper(s, i, acc) == ParseIntHelperCorrect(s, i, acc)
    decreases |s| - i
{
    if i < |s| {
        if s[i] == '\n' || s[i] == ' ' {
            // Base case, both return acc
        }
        else if !IsDigit(s[i]) {
            ParseIntHelperEquivalent(s, i + 1, acc);
        } else { // IsDigit(s[i])
            ParseIntHelperEquivalent(s, i + 1, acc * 10 + (s[i] as int - '0' as int));
        }
    }
}

lemma ParseIntFunc_Correct(s: string)
    requires |s| > 0
    ensures ParseIntFunc(s) == ParseIntHelperCorrect(s, 0, 0)
{
    ParseIntHelperEquivalent(s, 0, 0);
}

lemma IntToStringHelper_Correct(n: int, acc: string, res: string)
    requires n >= 0
    requires res == IntToStringHelper(n, acc)
    ensures |res| >= |acc|
    ensures n == 0 ==> res == acc
    ensures n > 0 ==> var s' := IntToStringHelper(n / 10, [(('0' as int) + (n % 10)) as char] + acc);
                        res == s'
{
    if n > 0 {
        var digit := n % 10;
        var digitChar := ('0' as int + digit) as char;
        IntToStringHelper_Correct(n / 10, [digitChar] + acc, IntToStringHelper(n / 10, [digitChar] + acc));
    }
}

lemma IntToStringFunc_Eq(n: int)
    requires n >= 0
    ensures n == 0 ==> IntToStringFunc(n) == "0"
    ensures n > 0 ==> var res := IntToStringFunc(n);
                      res == IntToStringHelper(n, "")
{
    if n == 0 { }
    else {
        IntToStringHelper_Correct(n, "", IntToStringFunc(n));
    }

}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    ensures |output| > 0
    ensures output[|output|-1] == '\n'
    ensures var h := ParseIntFunc(stdin_input);
            ValidInput(h) ==> output == IntToStringFunc(ComputeAttacks(h)) + "\n"
// </vc-spec>
// <vc-code>
{
    var h := ParseIntFunc(stdin_input);
    if ValidInput(h) {
        var attacks := ComputeAttacks(h);
        output := IntToStringFunc(attacks) + "\n";
    } else {
        // Fallback for invalid input, though problem statement implies valid only
        // or expects general robustness.
        // For this specific problem interpretation, since valid input implies success as per postcondition,
        // any other input could lead to any output as long as it matches the |output| > 0 and ends in \n
        output := "0\n";
    }
}
// </vc-code>

