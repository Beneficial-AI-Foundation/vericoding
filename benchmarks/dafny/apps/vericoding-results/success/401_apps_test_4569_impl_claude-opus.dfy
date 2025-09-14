predicate ValidWeather(weather: string)
{
    weather == "Sunny" || weather == "Cloudy" || weather == "Rainy"
}

function TrimNewline(input: string): string
{
    if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input
}

function NextWeather(weather: string): string
    requires ValidWeather(weather)
{
    if weather == "Sunny" then "Cloudy"
    else if weather == "Cloudy" then "Rainy"
    else "Sunny"
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures var trimmed := TrimNewline(input);
            if ValidWeather(trimmed) then 
                result == NextWeather(trimmed) + "\n"
            else 
                result == ""
// </vc-spec>
// <vc-code>
{
    var trimmed := TrimNewline(input);
    if ValidWeather(trimmed) {
        result := NextWeather(trimmed) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

