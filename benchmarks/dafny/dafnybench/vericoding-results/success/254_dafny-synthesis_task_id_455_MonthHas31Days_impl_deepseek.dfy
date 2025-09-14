

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MonthHas31Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
// </vc-spec>
// <vc-code>
{
    match month {
        case 1 => result := true;
        case 3 => result := true;
        case 5 => result := true;
        case 7 => result := true;
        case 8 => result := true;
        case 10 => result := true;
        case 12 => result := true;
        case _ => result := false;
    }
}
// </vc-code>

