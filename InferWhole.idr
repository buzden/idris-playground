-- Taken from https://www.reddit.com/r/Idris/comments/hngthh/why_idris_need_type_definition/

record Person where
    constructor MkPerson
    firstName, middleName, lastName : String
    age : Int

fred : ? -- Person
fred = MkPerson "Fred" "Joe" "Bloggs" 30
