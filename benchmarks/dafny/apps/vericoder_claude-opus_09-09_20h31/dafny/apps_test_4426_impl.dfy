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
    match day {
        case "SUN" => result := 7;
        case "MON" => result := 6;
        case "TUE" => result := 5;
        case "WED" => result := 4;
        case "THU" => result := 3;
        case "FRI" => result := 2;
        case "SAT" => result := 1;
    }
}
// </vc-code>

