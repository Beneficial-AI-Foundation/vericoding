// <vc-preamble>
predicate ValidDay(day: string) {
    day in ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"]
}

function DaysUntilSunday(day: string): int
    requires ValidDay(day)
{
    match day
    case "SUN" => 7
    case "MON" => 6  
    case "TUE" => 5
    case "WED" => 4
    case "THU" => 3
    case "FRI" => 2
    case "SAT" => 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DaysToNextSunday(day: string) returns (result: int)
    requires ValidDay(day)
    ensures result >= 1 && result <= 7
    ensures result == DaysUntilSunday(day)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
