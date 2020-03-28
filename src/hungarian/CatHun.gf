concrete CatHun of Cat = CommonX ** open ResHun, Prelude in {

  flags optimize=all_subs ;

  lincat

--2 Sentences and clauses
-- Constructed in SentenceHun, and also in IdiomHun

    S  = ResHun.Sentence ;
    QS = SS ;
    RS = SS ;
    -- relative sentence. Tense and polarity fixed,
    -- but agreement may depend on the CN/NP it modifies.

    Cl = ResHun.ClSlash ;
    ClSlash = ResHun.ClSlash ;
    SSlash  = ResHun.Sentence ; -- sentence missing NP; e.g. "she has looked at"
    Imp     = {s : Number => Polarity => Str} ; -- imperative             e.g. "look at this"

--2 Questions and interrogatives

-- Constructed in QuestionHun.

    QCl = ResHun.QClause ;
    IComp = SS ;                -- interrogative complement of copula  e.g. "where"
    IDet = ResHun.Determiner ;  -- interrogative determiner            e.g. "how many"
    IQuant = ResHun.Quant ;     -- interrogative quantifier            e.g. "which"
    IP = ResHun.NounPhrase ;    -- interrogative pronoun               e.g. "who"

--2 Subord clauses and pronouns

    --RCl = ResHun.RClause ;
    --RP = SS ;

--2 Verb phrases

-- Constructed in VerbHun.

    VP = ResHun.VerbPhrase ;
    VPSlash = ResHun.VPSlash ;
    Comp = ResHun.VerbPhrase ;


--2 Adjectival phrases

-- Constructed in AdjectiveHun.

    AP = ResHun.Adjective ;


--2 Nouns and noun phrases

-- Constructed in NounHun.
-- Many atomic noun phrases e.g. "everybody"
-- are constructed in StructuralHun.
-- The determiner structure is
-- ``` Predet (QuantSg | QuantPl Num) Ord
-- as defined in NounHun.

    CN = ResHun.Noun ;
    NP = ResHun.NounPhrase ;
    Pron = ResHun.Pronoun ; --Pronouns need enough info to turn it into NP or Quant.
    Det = ResHun.Determiner ;
    Predet = {s : Str} ;
    Quant = ResHun.Quant ;
    Num = ResHun.Num ;
    Ord = {
      s : Str ; -- Number => Case => Str ; -- Ord can come from AP and become AP again
      n : Number -- Ord can come from Num, which has inherent number
      } ;
    DAP = ResHun.Determiner ;


--2 Numerals

-- Constructed in NumeralHun.

    Card = ResHun.Num ;
    Numeral = ResHun.Numeral ;
    Digits = {s : CardOrd => Str ; n : Number} ;



--2 Structural words

-- Constructed in StructuralHun.
    Conj = ResHun.Conj ;
    Subj = SS ;
    Prep = ResHun.Postposition ;



--2 Words of open classes

-- These are constructed in LexiconHun and in
-- additional lexicon modules.

    VS,    -- sentence-complement verb            e.g. "claim"
    -- TODO: eventually different lincats
    VQ,    -- question-complement verb            e.g. "wonder"
    VA,    -- adjective-complement verb           e.g. "look"
    V = ResHun.Verb ;

    VV,    -- verb-phrase-complement verb         e.g. "want"
    V2A,   -- verb with NP and AP complement      e.g. "paint"
    V2V,   -- verb with NP and V complement       e.g. "cause"
    V2S,   -- verb with NP and S complement       e.g. "tell"
    V2Q,   -- verb with NP and Q complement       e.g. "ask"
    V2 = ResHun.Verb2 ;
    V3 = ResHun.Verb3 ;

    A = ResHun.Adjective ;
    A2  = ResHun.Adjective ;

    N,
    N2,
    N3 = ResHun.Noun ;
    PN = ResHun.NounPhrase ;

}
