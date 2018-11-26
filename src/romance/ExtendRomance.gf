incomplete concrete ExtendRomance of Extend = Cat **
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

    GenRP = variants {} ;     -- Num -> CN -> RP ; -- whose car

    GenModNP num np cn = DetCN (DetQuant (GenNP (lin NP np)) num) cn ;

    GenModIP num ip cn = IdetCN (IdetQuant (GenIP (lin IP ip)) num) cn ;

    CompBareCN cn = {
      s = \\agr => cn.s ! agr.n ;
      cop = serCopula
      } ;

    StrandQuestSlash = QuestSlash ; -- whom does John live with ; DEFAULT with whom does John live
    StrandRelSlash = RelSlash ; -- that he lives in ; DEFAULT in which he lives

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
    MkVPS2 = variants {} ;     --     : Temp -> Pol -> VPSlash -> VPS2 ;  -- has loved
    ConjVPS2 = variants {} ;     --   : Conj -> [VPS2] -> VPS2 ;          -- has loved and now hates
    ComplVPS2 = variants {} ;     --  : VPS2 -> NP -> VPS ;               -- has loved and now hates that person

    MkVPI2 = variants {} ;     --     : Ant  -> Pol -> VPSlash -> VPI2 ;  -- to have loved
    ConjVPI2 = variants {} ;     --   : Conj -> [VPI2] -> VPI2 ;          -- to love and have hated
    ComplVPI2 = variants {} ;     --  : VPI2 -> NP -> VPI ;               -- to love and hate that person

  lin
    ProDrop = E.ProDrop ;

    ICompAP = variants {} ;     -- AP -> IComp ; -- "how old"
    IAdvAdv = variants {} ;     -- Adv -> IAdv ; -- "how often"

    CompIQuant = E.CompIQuant ;

    PrepCN prep cn = E.PrepCN ;

  lin
    FocusObj = variants {} ;     -- NP -> SSlash -> Utt ; -- her I love
    FocusAdv = variants {} ;     -- Adv -> S -> Utt ; -- today I will sleep
    FocusAdV = variants {} ;     -- AdV -> S -> Utt ; -- never will I sleep
    FocusAP = variants {} ;     -- AP -> NP -> Utt ; -- green was the tree

    PresPartAP vp = {
      s = \\af => gerVP vp (aform2aagr af ** {p = P3}) ;
      isPre = False
      } ;

    EmbedPresPart = variants {} ;     -- VP -> SC ; -- looking at Mary (is fun)

    PastPartAP vps = pastPartAP vps [] ;

    PastPartAgentAP vps np = pastPartAP vps
      (let by = <Grammar.by8agent_Prep : Prep> in by.s ++ (np.s ! by.c).ton) ;

    PassVPSlash = E.PassVPSlash ;
    PassAgentVPSlash = E.PassAgentVPSlash ;

    NominalizeVPSlashNP = variants {} ;     -- VPSlash -> NP -> NP ;

    ExistsNP = ExistNP ;     -- NP -> Cl ; -- there exists a number / there exist numbers
    ExistCN cn = ExistNP (DetCN (DetQuant IndefArt NumSg) cn) ;
    ExistMassCN cn = ExistNP (MassNP cn) ;
    ExistPluralCN cn = ExistNP (DetCN (DetQuant IndefArt NumPl) cn) ;

    PurposeVP vp = {
      s = infVP vp (Ag Masc Sg P3)
      } ;

    ComplBareVS = ComplVS ;     -- VS -> S -> VP ; -- say she runs ; DEFAULT say that she runs

    SlashBareV2S = SlashV2S ;     -- V2S -> S -> VPSlash ; -- answer (to him) it is good ; DEFAULT answer that it is good

    ComplDirectVS vs utt = AdvVP (UseV <lin V vs : V>) (lin Adv {s = ":" ++ quoted utt.s}) ; -- DEFAULT complement added as Adv in quotes
    ComplDirectVQ vq utt = AdvVP (UseV <lin V vq : V>) (lin Adv {s = ":" ++ quoted utt.s}) ; -- DEFAULT complement added as Adv in quotes

    FrontComplDirectVS = variants {} ; -- NP -> VS -> Utt -> Cl ;      -- "I am here", she said
    FrontComplDirectVQ  = variants {} ; -- NP -> VQ -> Utt -> Cl ;      -- "where", she asked

    PredAPVP ap vp = ImpersCl (UseComp (CompAP (SentAP ap (EmbedVP vp)))) ; -- DEFAULT it is (good to walk)

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
    ReflRNP = variants {} ;     -- VPSlash -> RNP -> VP ; -- love my family and myself

    ReflPron = variants {} ;     -- RNP ; -- myself
    ReflPoss = variants {} ;     -- Num -> CN -> RNP ; -- my car(s)

    PredetRNP = variants {} ;     -- Predet -> RNP -> RNP ; -- all my brothers

    ConjRNP = variants {} ;     -- Conj -> RNPList -> RNP ; -- my family, John and myself

    Base_rr_RNP = variants {} ;     -- RNP -> RNP -> RNPList ; -- my family, myself
    Base_nr_RNP = variants {} ;     -- NP -> RNP -> RNPList ; -- John, myself
    Base_rn_RNP = variants {} ;     -- RNP -> NP -> RNPList ; -- myself, John
    Cons_rr_RNP = variants {} ;     -- RNP -> RNPList -> RNPList ; -- my family, myself, John
    Cons_nr_RNP = variants {} ;     -- NP -> RNPList -> RNPList ; -- John, my family, myself

    ComplGenVV = variants {} ;     -- VV -> Ant -> Pol -> VP -> VP ; -- want not to have slept

    CompoundN = variants {} ;     -- N -> N -> N ; -- control system / controls system / control-system
    CompoundAP = variants {} ;     -- N -> A -> AP ; -- language independent / language-independent

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
    WithoutVP = variants {} ;     -- VP -> Adv ; -- without publishing the document
    ByVP = variants {} ;     -- VP -> Adv ; -- by publishing the document
    InOrderToVP = variants {} ;     -- VP -> Adv ; -- (in order) to publish the document

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

    CompS = variants {} ;     -- S -> Comp ; -- (the fact is) that she sleeps
    CompQS = variants {} ;     -- QS -> Comp ; -- (the question is) who sleeps
    CompVP = variants {} ;     -- Ant -> Pol -> VP -> Comp ; -- (she is) to go

    UncontractedNeg = variants {} ;
    UttVPShort = UttVP ;
    ComplSlashPartLast = ComplSlash ;

    DetNPMasc = DetNP ;
    DetNPFem = DetNP ;

    iFem_Pron = i_Pron ; -- DEFAULT I (masc)
    youFem_Pron = youSg_Pron ; -- DEFAULT you (masc)
    weFem_Pron = we_Pron ;  -- DEFAULT we (masc)
    youPlFem_Pron = youPl_Pron ;  -- DEFAULT you plural (masc)
    theyFem_Pron = they_Pron ;  -- DEFAULT they (masc)
    youPolFem_Pron = youPol_Pron ;  -- DEFAULT you polite (masc)
    youPolPl_Pron = youPl_Pron ;  -- DEFAULT you plural (masc)
    youPolPlFem_Pron = youPl_Pron ;  -- DEFAULT you plural (masc)

    UttAccNP = UttNP ; -- him (accusative) ; DEFAULT he
    UttDatNP np = UttAccNP (lin NP np) ; -- him(dative) ; DEFAULT he
    UttAccIP = UttIP ; -- whom (accusative) ; DEFAULT who
    UttDatIP ip = UttAccIP (lin IP ip) ; -- whom (dative) ; DEFAULT who

} ;
