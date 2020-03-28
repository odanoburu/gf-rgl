concrete AdjectiveHun of Adjective = CatHun ** open ResHun, Prelude in {

  flags optimize=all_subs ;

  lin

  -- : A  -> AP ;
  PositA a = a ;

  -- : A  -> NP -> AP ;
  -- ComparA a np = a ** {
  --
  --   } ;

  -- : A2 -> NP -> AP ;  -- married to her
  -- ComplA2 a2 np = a2 ** { } ;

  -- : A2 -> AP ;        -- married to itself
  -- ReflA2 a2 = a2 ** { } ;

  -- : A2 -> AP ;        -- married
  -- UseA2 = PositA ;

  -- : A  -> AP ;     -- warmer
  -- UseComparA a = a ** {
  --   s = \\af => "???" ++ a.s ! af ;
  --   compar = []
  --  } ;


  -- : CAdv -> AP -> NP -> AP ; -- as cool as John
  -- CAdvAP adv ap np = ap ** { } ;

-- The superlative use is covered in $Ord$.

  -- : Ord -> AP ;       -- warmest
  AdjOrd ord = ord ** {
    s = \\_ => ord.s ;
    } ;

-- Sentence and question complements defined for all adjectival
-- phrases, although the semantics is only clear for some adjectives.

  -- : AP -> SC -> AP ;  -- good that she is here
  -- SentAP ap sc = ap ** {} ;

-- An adjectival phrase can be modified by an *adadjective*, such as "very".

  -- : AdA -> AP -> AP ;
  AdAP ada ap = ap ** {s = \\af => ada.s ++ ap.s ! af} ;


-- It can also be postmodified by an adverb, typically a prepositional phrase.

  -- : AP -> Adv -> AP ; -- warm by nature
  -- AdvAP  ap adv = ap ** {} ;

}
