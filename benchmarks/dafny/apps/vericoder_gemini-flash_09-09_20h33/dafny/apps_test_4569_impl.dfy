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
predicate {:private} MethodHelper(input: string, output: string)
{
    var trimmed := TrimNewline(input);
    if ValidWeather(trimmed) then
        output == NextWeather(trimmed) + "\n"
    else
        output == ""
}
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
    var trimmed_input := TrimNewline(input);
    if ValidWeather(trimmed_input) {
        result := NextWeather(trimmed_input) + "\n";
    } else {
        result := "";
    }
}
// </vc-code>

