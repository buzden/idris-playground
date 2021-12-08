-- Based on the code questioned at https://discord.com/channels/827106007712661524/834611018775789568/918166736153501696

a : String -> String -> Elab ()
a fn fd = declare
  `[ %foreign ~(IPrimVal EmptyFC $ Constant $ Str fd)
     ~(IVar EmptyFC $ UN $ Basic fn) : Int -> Int
   ]
