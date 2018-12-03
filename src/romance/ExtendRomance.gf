incomplete concrete ExtendRomance of Extend = Cat,
  ExtendFunctor - [
    GenNP,
      GenIP,
      GenModNP,
      GenModIP,
      CompBareCN,
      EmptyRelSlash,
      VPS,
      ListVPS,
      BaseVPS,
      ConsVPS,
      MkVPS,
      ConjVPS,
      PredVPS,
      VPI,
      ListVPI,
      BaseVPI,
      ConsVPI,
      MkVPI,
      ConjVPI,
      ComplVPIVV,
      ProDrop,
      CompIQuant,
      PrepCN,
      PresPartAP,
      PastPartAgentAP,
      PassVPSlash,
      PassAgentVPSlash,
      PurposeVP,
      AdjAsCN,
      AdjAsNP,
      RNP,
      RNPList,
      GerunCN,
      GerundNP,
      GerundAdv,
      ApposNP,
      AdAdV,
      UttAdV,
      PositAdVAdj,
      UttVPShort
    ]
  **
  open Grammar, Coordination, CommonRomance, (E = ExtraRomance), ResRomance in {

  lin
    GenNP np =
      let denp = (np.s ! ResPor.genitive).ton in {
        s = \\_,_,_,_ => [] ;
        sp = \\_,_,_ => denp ;
        s2 = denp ;
        isNeg = False ;
      } ;

    GenIP ip = {s = \\_,_,c => ip.s ! c} ;

    GenModNP num np cn = DetCN (DetQuant (GenNP (lin NP np)) num) cn ;

    GenModIP num ip cn = IdetCN (IdetQuant (GenIP (lin IP ip)) num) cn ;

    CompBareCN cn = {
      s = \\agr => cn.s ! agr.n ;
      cop = serCopula
      } ;

    EmptyRelSlash cls = {
      s = \\agr,t,a,p,m => cls.s ! agr ! DDir ! t ! a ! p ! m ++ cls.c2.s ;
      c = Nom
      } ;

  lincat
    VPS = E.VPS ;
    [VPS] = E.ListVPS ;
  lin
    BaseVPS = E.BaseVPS ;
    ConsVPS = E.ConsVPS ;

    MkVPS = E.MkVPS ;
    ConjVPS = E.ConjVPS ;
    PredVPS = E.PredVPS ;

  lincat
    VPI = E.VPI ;
    [VPI] = E.ListVPI ;

  lin
    BaseVPI = E.BaseVPI ;
    ConsVPI = E.ConsVPI ;

    MkVPI = E.MkVPI ;
    ConjVPI = E.ConjVPI ;
    ComplVPIVV = E.ComplVPIVV ;

  lin
    ProDrop = E.ProDrop ;

    CompIQuant = E.CompIQuant ;

    PrepCN prep cn = E.PrepCN ;

  lin
    PresPartAP vp = {
      s = \\af => gerVP vp (aform2aagr af ** {p = P3}) ;
      isPre = False
      } ;

    PastPartAP vps = pastPartAP vps [] ;

    PastPartAgentAP vps np = pastPartAP vps
      (let by = <Grammar.by8agent_Prep : Prep> in by.s ++ (np.s ! by.c).ton) ;

    PassVPSlash = E.PassVPSlash ;
    PassAgentVPSlash = E.PassAgentVPSlash ;

    PurposeVP vp = {
      s = infVP vp (Ag Masc Sg P3)
      } ;

    AdjAsCN ap = {
      s =\\n => ap.s ! AF Masc n ;
      g = Masc
      } ;

    AdjAsNP ap = heavyNP {
      s = \\_c => ap.s ! AF Masc Sg ;
      a = Ag Masc Sg P3
      } ;

  oper
    quoted : Str -> Str = \s -> "\"" ++ s ++ "\"" ; ---- TODO bind ; move to Prelude?

    pastPartAP : VPSlash -> Str -> AP ;
    pastPartAP vps agent = lin AP {
      s = \\af => vps.comp ! (aform2aagr af ** {p = P3}) ++ vps.s.s ! VPart (aform2gender af) (aform2number af) ++ agent ;
      isPre = False
      } ;

  lincat
    RNP = Grammar.NP ;
    RNPList = Grammar.ListNP ;

  lin
    GerundCN vp = {
      s = \\n => infVP vp {g = Masc ; n = n ; p = P3} ;
      g = Masc
      } ;
    GerundNP vp = let
      neutrAgr = Ag Masc Sg P3
      in heavyNP {
        s = \\_ => gerVP vp neutrAgr ;
        a = neutrAgr
      } ;
    GerundAdv vp = {
      s = gerundStr vp
      } ;

  oper
    gerundStr : VP -> Str ;
    gerundStr vp = gerVP vp (Ag Masc Sg P3) ;

  lin
    ApposNP np1 np2 = np1 ** {
      s = \\c => {
        c1 = (np1.s ! c).c1  ++ (np2.s ! c).c1 ;
        c2 = (np1.s ! c).c2 ++ (np2.s ! c).c2 ;
        comp = (np1.s ! c).comp ++ (np2.s ! c).comp ;
        ton = (np1.s ! c).ton ++ (np2.s ! c).ton
        } ;
      } ;

    AdAdV aa av = {
      s = aa.s ++ av.s
      } ;
    UttAdV av = av ;
    PositAdVAdj a = {
      s = a.s ! Posit ! AA
      } ;

    UttVPShort = UttVP ;

} ;
