Compare scores of two contestants Misha and Vasya in a programming contest.
Misha solved a problem worth 'a' points and submitted it 'c' minutes after start.
Vasya solved a problem worth 'b' points and submitted it 'd' minutes after start.
Scoring formula: max(3p/10, p - p*t/250) where p is original points, t is time.
Return "Misha", "Vasya", or "Tie" based on who scored higher.

predicate ValidInput(a: int, b: int, c: int, d: int)
{
    250 <= a <= 3500 && a % 250 == 0 &&
    250 <= b <= 3500 && b % 250 == 0 &&
    0 <= c <= 180 &&
    0 <= d <= 180
}

function CalculateScore(points: int, time: int): real
    requires points >= 0 && time >= 0
{
    var min_score := 3.0 * points as real / 10.0;
    var time_adjusted := points as real - points as real * time as real / 250.0;
    if min_score >= time_adjusted then min_score else time_adjusted
}

predicate CorrectResult(a: int, b: int, c: int, d: int, result: string)
    requires ValidInput(a, b, c, d)
{
    var misha_score := CalculateScore(a, c);
    var vasya_score := CalculateScore(b, d);
    (result == "Misha" <==> misha_score > vasya_score) &&
    (result == "Vasya" <==> vasya_score > misha_score) &&
    (result == "Tie" <==> misha_score == vasya_score)
}

function MaxReal(x: real, y: real): real
{
    if x >= y then x else y
}

method DetermineWinner(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures result == "Misha" || result == "Vasya" || result == "Tie"
    ensures CorrectResult(a, b, c, d, result)
{
    var misha_score := CalculateScore(a, c);
    var vasya_score := CalculateScore(b, d);
    
    if misha_score > vasya_score {
        result := "Misha";
    } else if vasya_score > misha_score {
        result := "Vasya";
    } else {
        result := "Tie";
    }
}
