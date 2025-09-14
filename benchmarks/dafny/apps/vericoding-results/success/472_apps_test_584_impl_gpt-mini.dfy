function IsLetter(c: char): bool
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

predicate ValidParentheses(input: string)
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then true
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        IsValidParenthesesSequence(s, 0, 0)
}

predicate IsValidParenthesesSequence(s: string, pos: int, balance: int)
    requires 0 <= pos <= |s|
    requires balance >= 0
    decreases |s| - pos
{
    if pos >= |s| then balance == 0
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then balance - 1 
                         else balance;
        newBalance >= 0 && IsValidParenthesesSequence(s, pos + 1, newBalance)
}

function LongestWordOutside(input: string): int
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then 0
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        ComputeLongestOutside(s, 0, 0, 0, 0)
}

function CountWordsInside(input: string): int
{
    var newlinePos := FindNewline(input);
    if newlinePos >= |input| then 0
    else
        var s := if newlinePos + 1 < |input| then input[newlinePos + 1..] else "";
        ComputeCountInside(s, 0, 0, 0)
}

predicate ValidOutput(input: string, len_out: int, count_in: int)
{
    len_out >= 0 && count_in >= 0 &&
    len_out == LongestWordOutside(input) &&
    count_in == CountWordsInside(input)
}

function FindNewline(input: string): int
    ensures 0 <= FindNewline(input) <= |input|
{
    FindNewlineHelper(input, 0)
}

function FindNewlineHelper(input: string, pos: int): int
    requires 0 <= pos <= |input|
    ensures pos <= FindNewlineHelper(input, pos) <= |input|
    decreases |input| - pos
{
    if pos >= |input| then pos
    else if input[pos] == '\n' then pos
    else FindNewlineHelper(input, pos + 1)
}

function ComputeLongestOutside(s: string, pos: int, balance: int, cur: int, best: int): int
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0 && best >= 0
    ensures ComputeLongestOutside(s, pos, balance, cur, best) >= 0
    decreases |s| - pos
{
    if pos >= |s| then
        if cur > best && balance == 0 then cur else best
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then (if balance > 0 then balance - 1 else 0)
                         else balance;
        var newCur := if IsLetter(c) then cur + 1
                     else if cur > 0 then 0
                     else cur;
        var newBest := if !IsLetter(c) && cur > 0 && balance == 0 then
                          if cur > best then cur else best
                      else best;
        ComputeLongestOutside(s, pos + 1, newBalance, newCur, newBest)
}

function ComputeCountInside(s: string, pos: int, balance: int, cur: int): int
    requires 0 <= pos <= |s|
    requires balance >= 0
    requires cur >= 0
    ensures ComputeCountInside(s, pos, balance, cur) >= 0
    decreases |s| - pos
{
    if pos >= |s| then 0
    else
        var c := s[pos];
        var newBalance := if c == '(' then balance + 1 
                         else if c == ')' then (if balance > 0 then balance - 1 else 0)
                         else balance;
        var newCur := if IsLetter(c) then cur + 1
                     else if cur > 0 then 0
                     else cur;
        var wordEnded := !IsLetter(c) && cur > 0;
        var countIncrement := if wordEnded && balance > 0 then 1 else 0;
        countIncrement + ComputeCountInside(s, pos + 1, newBalance, newCur)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: (int, int))
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == '\n'
    requires forall i :: 0 <= i < |input| ==> (IsLetter(input[i]) || input[i] == '_' || input[i] == '(' || input[i] == ')' || input[i] == '\n' || input[i] == '\r' || ('0' <= input[i] <= '9'))
    requires ValidParentheses(input)
    ensures result.0 >= 0 && result.1 >= 0
    ensures result.0 == LongestWordOutside(input)
    ensures result.1 == CountWordsInside(input)
    ensures ValidOutput(input, result.0, result.1)
// </vc-spec>
// <vc-code>
{
  var len_out := LongestWordOutside(input);
  var count_in := CountWordsInside(input);
  result := (len_out, count_in);
}
// </vc-code>

