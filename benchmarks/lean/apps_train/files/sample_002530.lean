A marine themed rival site to Codewars has started. Codwars is advertising their website all over the internet using subdomains to hide or obfuscate their domain to trick people into clicking on their site.

Your task is to write a function that accepts a URL as a string and determines if it would result in an http request to codwars.com.

Function should return true for all urls in the codwars.com domain. All other URLs should return false.

The urls are all valid but may or may not contain http://, https:// at the beginning or subdirectories or querystrings at the end.

For additional confusion, directories in can be named "codwars.com" in a url with the codewars.com domain and vise versa. Also, a querystring may contain codewars.com or codwars.com for any other domain - it should still return true or false based on the domain of the URL and not the domain in the querystring. Subdomains can also add confusion: for example `http://codwars.com.codewars.com` is a valid URL in the codewars.com domain in the same way that `http://mail.google.com` is a valid URL within google.com

Urls will not necessarily have either codewars.com or codwars.com in them. The folks at Codwars aren't very good about remembering the contents of their paste buffers.

All urls contain domains with a single TLD; you need not worry about domains like company.co.uk.

```
findCodwars("codwars.com"); // true
findCodwars("https://subdomain.codwars.com/a/sub/directory?a=querystring"); // true
findCodwars("codewars.com"); // false
findCodwars("https://subdomain.codwars.codewars.com/a/sub/directory/codwars.com?a=querystring"); // false
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded