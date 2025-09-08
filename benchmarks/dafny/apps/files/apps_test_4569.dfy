Given today's weather from a 3-day repeating cycle (Sunny → Cloudy → Rainy → Sunny → ...), determine tomorrow's weather.

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

method solve(input: string) returns (result: string)
    ensures var trimmed := TrimNewline(input);
            if ValidWeather(trimmed) then 
                result == NextWeather(trimmed) + "\n"
            else 
                result == ""
{
    var trimmed := TrimNewline(input);

    if ValidWeather(trimmed) {
        result := NextWeather(trimmed) + "\n";
    } else {
        result := "";
    }
}
