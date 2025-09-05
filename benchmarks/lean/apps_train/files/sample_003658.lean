```if-not:sql
Implement a function that receives two IPv4 addresses, and returns the number of addresses between them (including the first one, excluding the last one).
```

```if:sql
Given a database of first and last IPv4 addresses, calculate the number of addresses between them (including the first one, excluding the last one).

## Input

~~~
---------------------------------
|     Table    | Column | Type  |
|--------------+--------+-------|
| ip_addresses | id     | int   |
|              | first  | text  |
|              | last   | text  |
---------------------------------
~~~

## Output

~~~
----------------------
|   Column    | Type |
|-------------+------|
| id          | int  |
| ips_between | int  |
----------------------
~~~
```

All inputs will be valid IPv4 addresses in the form of strings. The last address will always be greater than the first one.

___

## Examples

```python
ips_between("10.0.0.0", "10.0.0.50")  ==   50 
ips_between("10.0.0.0", "10.0.1.0")   ==  256 
ips_between("20.0.0.10", "20.0.1.0")  ==  246
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded