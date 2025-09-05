In Spanish, the conjugated verb changes by adding suffixes and according to the person we're talking about. There's something similar in English when we talk about "She", "He"or "It" (3rd person singular):

With the verb "run":

**He / She / It runS**

As you can see, the rule (at least with regular verbs) is to add the suffix  "-s" in the 3rd person singular. In Spanish it works the same way but we need to remove the **infinitive suffix** and add a specific suffix to all the others persons (I, You, He/She/It, We, You, They).

Verbs in Spanish and the infinitive suffix.
--

In Spanish we assume a verb is on its infitive form when it has one of the infinitives suffixes (**AR**, **ER** or **IR**) at the end:

- Com**er** -> to eat

- Camin**ar** -> to walk

- Viv**ir** -> to live

## How to conjugate

For conjugating in Spanish, we need to remove the infinitive suffix (**ar**, **er** *or* **ir**) and add the personal suffixes corresponding to the person we're talking to. In this kata we'll conjugate the verbs to its **presente indicativo** (simple present) form.

Personal suffixes
--
The personal suffixes changes depending of the **Infinitive suffix**.

If the infinitive suffix is **AR** the personal suffixes are:

- first person singular (Yo / I): -**o**
- second person singular (Tú / You): -**as**
- third person singular (Él, Ella / He, She): -**a**
- first person plural (Nosotros / We): -**amos**
- second person plural (Vosotros / You): -**áis**
- third person plural (Ellos / They): -**an**

If the infinitive suffix is **ER**:
- first person singular (Yo / I): -**o**
- second person singular (Tú / You): -**es**
- third person singular (Él, Ella / He, She): -**e**
- first person plural (Nosotros / We): -**emos**
- second person plural (Vosotros / You): -**éis**
- third person plural (Ellos / They): -**en**

If the infinitive suffix is **IR**:
- first person singular (Yo / I): -**o**
- second person singular (Tú / You): -**es**
- third person singular (Él, Ella / He, She): -**e**
- first person plural (Nosotros / We): -**imos**
- second person plural (Vosotros / You): -**ís**
- third person plural (Ellos / They): -**en**

## Conjugating 
Steps for conjugating:
1. Remove the infinitive suffix (ar, er, ir)
2. And add the personal suffixes
- Example: verb **Caminar** (to walk)
  - Camin**o** (I walk)
  - Camin**as** (You walk)
  - Camin**a** (He walks)
  - Camin**amos** (We walk)
  - Camin**áis** (You guys walk)
  - Camin**an** (They walk)
- Example: verb **Comer** (to eat):
  - Com**o** (I eat)
  - Com**es** (You eat)
  - Com**e** (He, She eats)
  - Com**emos** (We eat)
  - Com**éis** (You guys eat)
  - Com**en** (They eat)
- Example: verb **Vivir** (to live):
  - Viv**o** (I live)
  - Viv**es** (You live)
  - Viv**e** (He, She lives)
  - Viv**imos** (We live)
  - Viv**ís** (You guys live)
  - Viv**en** (They live)

## Your Task

You need to write a function called **conjugate** which will return an object with a spanish verb conjugated. The object must look like this:

```
{
  "comer": [
    "como",
    "comes",
    "come",
    "comemos",
    "coméis",
    "comen"
  ]
}

```

Where the key is the verb in its original form (infinitive form) and its value will be an array with the conjugations.

Another example:
```
{
  "vivir": [
    "vivo",
    "vives",
    "vive",
    "vivimos",
    "vivís",
    "viven"
  ]
}

```

## Notes:
1. The conjugations must be in this order:
```
{
    verb: [
      "first person singular",
      "second person singular",
      "third person singular",
      "first person plural",
      "second person plural",
      "third person plural"
    ]
}
```
2.Don't use `JSON.stringify(obj, null, 2)` because the "presentation" of the object isn't important.

3.Don't use accents in Python version

 **Buena suerte!**
---

def conjugate (verb : String) : String × Conjugations :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
