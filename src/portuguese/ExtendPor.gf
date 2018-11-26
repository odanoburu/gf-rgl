--# -path=alltenses:../common:../abstract:../romance

concrete ExtendPor of Extend =
  CatPor ** ExtendRomance -
  [
    ICompAP,
      IAdvAdv,
      CompoundN,
      CompoundAP,
      WithoutVP,
      ByVP,
      InOrderToVP,
      CompVP,
      iFem_Pron,
      weFem_Pron,
      youFem_Pron,
      youPlFem_Pron,
      youPolPl_Pron,
      youPolFem_Pron,
      youPolPlFem_Pron,
      theyFem_Pron
   ]
  -- don't forget to put the names of your own
                       -- definitions here
  with
    (Grammar = GrammarPor), (Syntax = SyntaxPor) **
  open
  GrammarPor,
  ResPor,
  MorphoPor,
  Coordination,
  Prelude,
  ParadigmsPor,
  (S = StructuralPor) in {

  lin
    ICompAP ap = {
      s =\\a => "o quão" ++ ap.s ! AF a.g a.n ;
      cop = serCopula
      } ;

    IAdvAdv adv = {
      s = "o quão" ++ adv.s
      } ;

  lin
    ExistsNP np =
      mkClause [] True False np.a
      (insertComplement (\\_ => (np.s ! Nom).ton)
         (predV (mkV "existir"))) ;

  lin
    CompoundN noun noun2 = {
      -- order is different because that's needed for correct
      -- translation from english
      s = \\n => noun2.s ! n
        ++ variants {"de" ; genForms "do" "da" ! noun.g}
        ++ noun.s ! Sg ;
      g = noun2.g
      } ;

    CompoundAP noun adj = {
      s = \\af => case af of {
        AF g n => adj.s ! Posit ! AF noun.g n ++ "de" ++ noun.s ! n ;
        -- do I need do(s)/da(s)?
        _ => adj.s ! Posit ! AF noun.g Sg ++ "de" ++ noun.s ! Sg
        } ;
      isPre = adj.isPre
      } ;

    WithoutVP vp = {
      s = "sem" ++ gerundStr vp
      } ;

    ByVP vp = {
      s = "por" ++ gerundStr vp
      } ;

    InOrderToVP vp = {
      s = "a fim de" ++ gerundStr vp
      } ;

    --TODO: actually use ant
    CompVP ant p vp = let
      neg = negation ! p.p
      in {
        s = \\agr => ant.s ++ p.s ++ "de" ++ neg.p1 ++ infVP vp agr ;
        cop = serCopula
      } ;

  oper
    gerundStr : VP -> Str ;
    gerundStr vp = gerVP vp (Ag Masc Sg P3) ;

  lin
    iFem_Pron = pronAgr S.i_Pron Fem Sg P1 ;
    weFem_Pron = pronAgr S.we_Pron Fem Pl P1 ;
    youFem_Pron = pronAgr S.youSg_Pron Fem Sg P3 ;
    youPlFem_Pron = pronAgr S.youPl_Pron Fem Pl P3 ;
    youPolPl_Pron = mkPronoun "vós" "vos" "vos" "vós"
      "vosso" "vossa" "vossos" "vossas"
      Masc Pl P2 ;
    youPolFem_Pron = pronAgr S.youPol_Pron Fem Sg P2 ;
    youPolPlFem_Pron = pronAgr youPolPl_Pron Fem Pl P2 ;
    theyFem_Pron = mkPronFrom S.they_Pron "elas" "as" "lhes" "elas" Fem Pl P3 ;

} ;
