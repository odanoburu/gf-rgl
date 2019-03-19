concrete ExtraLexCaesar of ExtraLexCaesarAbs = CatLat ** open Prelude,ParadigmsLat,ResLat, IrregLat, LexiconLat,StructuralLat in {
  lin
    a_Prep = mkPrep "a" Abl ;
    ab_Prep = mkPrep "ab" Abl ;
    abdere_V = mkV "abdere" "abdo" "abdidi" "abditum"; 
    abducere_V = mkV "abducere" "abduco" "abduxi" "abductum" ; -- prefixVerb "ab" ducere_V; -- ab + ducere, missing abduci (inf VInfPassPres : abduceri)
    abesse_V = prefixVerb "ab" be_V; -- ab + esse, missing absente?
    abicere_V = mkV "abicere" "abicio" "abieci" "abiectum"; -- prefixVerb "ab" iacere_V; -- ab + iacere
    abscisus_A = mkA "abscisus";
    absens_A = mkA "absens" "absentis"; -- missing absente
    absimilis_A = mkA "absimilis" "absimile"; -- missing absimili (s Posit (Ag Masc Sg Dat) : absimii)
    abstinere_V2 = mkV2 (mkV "abstinere"); -- prefixVerb2 "ab" tenere_V2 ; -- -- ab + tenere
    abstrahere_V2 = mkV2 (mkV "abstrahere" "abstraho" "abstraxi" "abstractum");-- prefixVerb2 "ab" trahere_V2 ; -- ab + trahere
--    ac_Conj = mkConj "" "ac" Sg ;
    accedere_V = mkV "adcedere" "adcedo" "adcessi" "adcessum"; -- prefixVerb "ad" cedere_V ; -- ad + cedere
    accendere_V = mkV "accendere" "accendo" "accendi" "accensum"; 
    accidere_V = mkV "accidere" "accido" "accidi" "accisum"; -- ad + caedere?
    accipere_V = mkV "accipere" "accipio" "accepi" "acceptum"; -- prefixVerb "ad" capere_V; -- ad + capere
    acclivis_A = mkA "acclivis" "acclive" ;
    acclivitas_N = mkN "acclivitas" "acclivitatis" feminine;
    accommodare_V = mkV "accommodare" ; 
    accommodatus_A = mkA "accommodatus" ;
    accurrere_V = mkV "accurrere" "accurro" "accucurri" "accursum"; -- prefixVerb "ad" currere_V; -- ad + currere
    accusare_V = mkV "accusare";
    acervus_N = mkN "acervus" ;
    acies_N = mkN "acies" ;
    acriter_Adv = ss "acriter"; -- comparison???
    ad_Prep = mkPrep "ad" Acc;
    adaequare_V = mkV "adaequare"; -- ad + aequare?
    adamare_V2 = mkV2 (mkV "adamare"); -- prefixVerb2 "ad" love_V2; -- ad + amare, missing adamassent (act (VAct VAnt (VImpf VConj) Pl P3) : adamavissent)?
    adducere_V = mkV "adducere" "adduco" "adduxi" "adductum"; -- prefixVerb "ad" ducere_V; -- ad + ducere, missing adduci
    adequitare_V = mkV "adequitare"; -- prefixVerb "ad" equitare_V; -- ad + equitare
    adesse_V = prefixVerb "ad" be_V; -- ad + esse
    adferre_V = prefixVerb "ad" ferre_V;-- ad + ferre
    adfectus_A = mkA "adfectus";
    adfectus_N = mkN "adfectus" "adfectus" masculine;
    adficere_V = mkV " adficere" "adfico" "adfeci" "adfectum"; -- ad + facere?, missing adficiebantur
    adfigere_V = mkV " adfigere" "adfixi" "adfixum"; -- ad + figere?, missing adfixae
    adfinitas_N = mkN "adfinitas" "adfinitatis" feminine;
    adflictare_V = mkV "adflictare";
    adflictus_A = mkA "adflictus";
    adgredi_V = mkV "adgredi" "adgredior" "adgressus"; -- ad + gradior?, missing adgressi, adgressus
    adgregare_V = mkV "adgregare"; -- ad + gregare?
    adhibere_V = mkV "adhibere"; -- ad + habere?
    adhuc_Adv = ss "adhuc";
    Adiatunnus_PN = mkPN (lin N (singularN (mkN "Adiatunnus")));
    adicere_V = mkV "adicere" "adieci" "adiectum"; -- ad + iacere?, missing adiecta
    adigere_V = mkV "adigere" "adigo" "adegi" "adactum"; -- ad + agere?, missing adigi
    adire_V = mkV "adire" "adeo" "" ""; -- prefixVerb "ad" ire_V; -- ad + ire, missing adiisset, aditus?
    aditus_N = mkN "aditus" "aditus" masculine;
    adiungere_V = mkV "adiungere" "adiungo" "adiunxi" "adiunctum"; -- ad + iungere?
    adiuvare_V = mkV "adiuvare"; -- ad + iuvare?
    administrare_V = mkV "administrare"; -- ad + ministrare
    admirari_V = mkV "admirari" "admiror" "admiratus"; -- ad + mirari?
    admittere_V = mkV "admittere" "admitto" "admisi" "admissum"; -- ad + mittere?
    admodum_Adv = ss "admodum";
    adoriri_V = mkV "adoriri" "adorior" "adortus"; -- ad + oriri?, missing adorti, adortum, adortus 
    adpellere_V = mkV "adpellere" "adpello" "adpuli" "adpulsum"; -- ad + pelere?
    adpetere_V = mkV "adpetere" "adpeto" "adpetivi" "adpetitum"; -- ad + petere?, missing adpetierit, adpetisse, adpetissent
    adpropinquare_V = mkV " adpropinquare"; -- ad + propinquare?
    -- adpulsare_V = mkV "adpulsare";
    adsciscere_V = mkV "adsciscere" "adscisco" "adscivi" "ascitum"; -- ad +  sciscere?
    adsuere_V = mkV "adsuere" "adsuo" "adsui" "adsutum"; -- ad + suere?, missing adsue
    adsuefacere_V = mkV "adsuefacere" "adsuefacio" "adsuefeci" "adsuefactum"; -- possibly problematic
    -- adtectus ???
    adulescentia_N = mkN "adulescentia";
    adulescentulus_N = mkN "adulescentulus";
    advenire_V = mkV "advenire" "advenio" "adveni" "adventum"; -- prefixVerb "ad" venire_V; -- ad + venire
    advertere_V = mkV "advertere" "adverto" "adverti" "adversum"; -- ad + vertere?
    adventus_N = mkN "adventus" "adventus" masculine;
    aedificare_V = mkV "aedificare";
    aedificium_N = mkN "aedificium";
    aeger_A = mkA "aeger";
    aegre_Adv = ss "aegre"; -- comparison?
    Aemilius_PN = mkPN (lin N (singularN (mkN "Aemilius")));
    aequaliter_Adv = ss "aequaliter";
    aequare_V = mkV " aequare";
    aequinoctium_N = mkN "aequinoctium";
    aequitas_N = mkN "aequitas" "aequitatis" feminine;
    aequum_N = mkN "aequum";
    aequus_A = mkA "aequus";
    aerarius_A = mkA "aerarius";
    aerarius_N = mkN "aerarius";
    aer_f_N = mkN "aer" "aeris" feminine;
    aer_m_N = mkN "aer" "aeris" masculine;
    aes_N = mkN "aer" "aeris" neuter;
    aestas_N = mkN "aestas" "aestatis" feminine;
    aestimare_V = mkV "aestimare";
    aestuarium_N = mkN "aestuarium";
    aestus_N = mkN "aestus" "aestus" masculine;
    aetas_N = mkN "aetas" "aetatis" feminine;
    ager_N = mkN "ager";
    agere_V = mkV "agere" "ago" "egi" "actum";
    agger_N = mkN "agger" "aggeris" masculine;
    agmen_N = mkN "agmen" "agminis" neuter;
    alacer_A = mkA "alacer" "alacris";
    alacritas_N = mkN "alacritas" "alacritatis" feminine;
    alarius_A = mkA "alarius";
    -- alduas_??? = ???;
    alere_1_V = mkV "alere" "alo" "alui" "altum";
    alere_2_V = mkV "alere" "alo" "alui" "alitum";
    alienus_A = mkA "alienus";
--    alii_Conj = mkConj "alii" "alii" Sg ;
    aliquam_Adv = ss "aliquam";
    aliquanto_Adv = ss "aliquanto";
    --aliqui_Pron = mkPron ???;
--    aliquis_Pron = aliquis;
    aliter_Adv = ss "aliter";
    alium_N = mkN "alium";
    alius_A = mkA (mkN "alius") (mkN "alia") (mkN "aliud" "alius" neuter);
    Allobroges_PN = mkPN (lin N (pluralN (mkNoun "" "" "" "" "" "" "Allobroges" "Allobroges" "Allobrogum" "Allobrogibus" masculine))); -- missing Allobrogas
    Alpes_PN = mkPN (lin N (pluralN (mkNoun "" "" "" "" "" "" "Alpes" "Alpes" "Alpium" "Alpibus" feminine)));
    alter_A = mkA (mkN "alter") (mkN "altera") (mkN "alterum"); -- missing alterius
    alterare_V = mkV "alterare";
    altitudo_N = mkN "altitudo" "altitudinis" feminine;
    altus_A = mkA "altus";
    aluta_N = mkN "aluta";
    Ambarri_PN = mkPN (lin N (pluralN (mkN "Ambarrus")));
    Ambiani_PN = mkPN (lin N (pluralN (mkN "Ambianus")));
    Ambiliati_PN = mkPN (lin N (pluralN (mkN "Ambiliatus")));
    Ambivariti_PN = mkPN (lin N (pluralN (mkN "Ambivaritus")));
    amentia_N = mkN "amentia";
    amicitia_N = mkN "amicitia";
    amicus_A = mkA "amicus";
    amittere_V = mkV "amittere" "amitto" "amisi" "amissum";
    amplificare_V = mkV "amplificare";
    amplitudo_N = mkN "amplitudo" "amplitudinis" feminine;
    amplus_A = mkA "amplus";
    anceps_A = mkA "anceps" "ancipitis";
    ancora_N = mkN "ancora";
    Andebrogius_PN = mkPN (lin N (singularN (mkN "Andebrogius")));
    --Andes_PN = ???
    angustia_N = mkN "angustia";
    angustiare_V = mkV "angustiare";
--    an_Conj = mkConj "" "an" Sg;
--    an_an_Conj = mkConj "an" "an" Sg;
    animadvertere_V = mkV "animadvertere" "animadverto" "animadverti" "animadversum";
    animus_N = mkN "animus";
    annuus_A = mkA "annuus";
    ante_Adv = ss "ante";
    ante_Prep = mkPrep "ante" Acc;
    antea_Adv = ss "antea";
    antecedere_V = mkV "antecedere" "antecedo" "antecessi" "antecessum"; -- ante + cedere?
    antemna_N = mkN "antemna";
    anteponere_V = mkV "anteponere" "antepono" "anteposui" "antepositum"; -- prefixVerb2 "ante" put_V2; -- ante + ponere
    antiquitus_Adv = ss "antiquitus";
    antiquus_A = mkA "antiquus"; -- missing antiquissimum
    aperire_V = mkV "aperire" "aperio" "aperui" "apertum"; -- missing aperta, apertis, apertissimis, apertissimo, aperto, apertum, apertus
    apertare_V = mkV "apertare";
    Aprilis_PN = mkPN (lin N (singularN (mkN "Aprilis" "Aprilis" masculine))); -- missing Apr, April
    appellare_V = mkV "appellare";
    aptus_A = mkA "aptus";
    apud_Prep = mkPrep "apud" Acc;
    aquatio_N = mkN "aquatio" "aquationis" feminine;
    aquila_N = mkN "aquila";
    Aquileia_PN = mkPN (lin N (singularN (mkN "Aquileia")));
    Aquitania_PN = mkPN (lin N (singularN (mkN "Aquitania")));
    Aquitanus_N = mkN "Aquitanus";
    Arar_PN = mkPN (lin N (singularN (mkN "Arar" "Araris" masculine))); -- missing Ararim
    arbitrari_V = mkV "arbitrari";
    arbitrium_N = mkN "arbitrium";
    arcessere_V = mkV "arcessere" "arcesso" "arcessivi" "arcessitum";
    arduus_A = mkA "arduus";
    aries_N = mkN "aries" "arietis" masculine;
    Ariovistus_PN = mkPN (lin N (singularN (mkN "Ariovistus")));
    armatus_A = mkA "armatus";
    arma_N = lin N (pluralN (mkNoun "" "" "" "" "" "" "arma" "arma" "armorum" "armis" neuter));
    armamentum_N = mkN "armamentum";
    armare_V = mkV "armare";
    armatura_N = mkN "armatura";
    armus_N = mkN "armus";
    arroganter_Adv = ss "arroganter"; -- comparison?
    arrogantia_N = mkN "arrogantia";
    artus_A = mkA "artus";
    Arverni_PN = mkPN (lin N (pluralN (mkN "Arvernus")));
    arx_N = mkN "arx" "arcis" feminine;
    ascendere_V = mkV "ascendere" "ascendo" "ascendi" "ascensum";
--    at_Conj = mkConj "at" "" Sg ;
--    atque_Conj = mkConj "atque" "" Sg ;
    Atrebates_PN = mkPN (mkN "Atrebas" "Atrebatis" masculine);
    attingere_V = mkV "attingere" "attingo" "attigi" "attactum"; -- ad + tangere?
    attribuere_V = mkV "attribuere" "attribuo" "attribui" "attributum"; -- ad + tribuere?, missing attribuant
    -- auctibus ???
    auctor_N = mkN "auctor" "auctoris" masculine;
    auctorare_V = mkV "auctorare";
    auctoritas_N = mkN "auctoritas" "auctoritatis" feminine;
    auctus_A = mkA "auctus";
    audacter_Adv = ss "audacter"; -- comparison?
    audax_A = mkA "audax" "audacis";
    audere_V = mkV "audere"; -- semi-deponent?, missing ausos
    audire_V = mkV "audire" ; -- missing audierant, audierit
    auditio_N = mkN "auditio" "auditionis" feminine;
    augere_V = mkV "augere"; -- missing auxisse
    Atuatuci_PN = mkPN (lin N (pluralN (mkN "Atuatucus")));
    Aulerci_PN = mkPN (lin N (pluralN (mkN "Aulercus")));
    Auriga_PN = mkPN (mkN "Auriga");
    Aurunculeius_PN = mkPN (lin N (singularN (mkN "Aurunculeius")));
    Ausci_PN = mkPN (lin N (pluralN (mkN "Auscus")));
--    aut_Conj = mkConj "aut" "" Sg ;
--    autem_Conj = mkConj "autem" "" Sg ;
    auxiliare_V = mkV "auxiliare";
    auxilium_N = mkN "auxilium";
    avaritia_N = mkN "avaritia";
    avertere_V = mkV "avertere" "averto" "averti" "aversum"; -- ab + vertere?, missing aventu (noun sg supine neut dat)
    avus_N = mkN "avus";
    Axona_PN = mkPN (lin N (singularN (mkN "Axona")));
    baculus_N = mkN "baculus";
    Baleares_PN = mkPN (lin N (pluralN (mkN "Balear" "Balearis" masculine)));
    barbarus_A = mkA "barbarus";
    barbarus_N = mkN "barbarus";
    batavus_A = mkA "batavus";
    Belgae_PN = mkPN (lin N (pluralN (mkN "Belga"))); -- missing Belgos
    bellare_V = mkV "bellare";
    bellicosus_A = mkA "bellicosus";
    Bellovaci_PN = mkPN (lin N (pluralN (mkN "Bellovacus")));
    bellum_N = mkN "bellum";
    bellus_A = mkA "bellus";
    bene_Adv = ss "bene"; -- comparison?
    beneficium_N = mkN "beneficium";
    Bibrax_PN = mkPN (lin N (singularN (mkN "Bibrax" "Bibractis" masculine)));
    biduum_N = mkN "biduum";
    biduus_A = mkA "biduus";
    biennis_A = mkA "biennis" "bienne"; -- missing biennium
    biennium_N = mkN "biennium";
    binus_A = mkA "binus";
    bipedalis_A = mkA "bipedalis" "bipedale"; -- missing bipedalibus
    bipertitus_A = mkA "bipertitus";
    bis_Adv = ss "bis";
    Biturix_PN = mkPN (lin N (pluralN (mkN "Biturix" "Biturigis" masculine)));
    -- boc ???
    Boduognatus_PN = mkPN (lin N (singularN (mkN "Boduognatus")));
    Boi_PN = mkPN (lin N (pluralN (mkN "Boius"))); -- missing Boi
    bonitas_N = mkN "bonitas" "bonitatis" feminine;
    bracchium_N = mkN "bracchium";
    Bratuspantium_PN = mkPN (lin N (singularN (mkN "Bratuspantium")));
    brevi_Adv = ss "brevi";
    breviare_V = mkV "breviare";
    brevis_A = mkA "brevis" "breve"; -- missing brevi
    brevitas_N = mkN "brevitas" "brevitatis" feminine;
    Britannia_PN = mkPN (mkN "Britannia");
    britannus_A = mkA "britannus";
    Brutus_PN = mkPN (lin N (singularN (mkN "Brutus")));
    cadaver_N = mkN "cadaver" "cadaveris" neuter;
    cadere_V = mkV "cadere" "cado" "cecidi" "casum";
    Caesar_PN = mkPN (lin N (singularN (mkN "Caesar" "Caesaris" masculine))); -- missing Caesare
    caespes_N = mkN "caespes" "caespitis" masculine;
    calamitas_N = mkN "calamitas" "calamitatis" feminine;
    calare_V = mkV "calare";
    calo_N = mkN "calo" "calonis" masculine;
    campus_N = mkN "campus";
    capere_V = mkV "capere" "capio" "cepi" "captum"; -- missing capi
    captivus_A = mkA "captivus";
    captivus_N = mkN "captivus";
    captus_N = mkN "captus" "captus" masculine;
    carina_N = mkN "carina";
    carpere_V = mkV "carpere" "carpio" "carpsi" "carptum";
    carrus_N = mkN "carrus";
    castellum_N = mkN "castellum";
    castra_N = lin N (pluralN (mkNoun "" "" "" "" "" "" "castra" "castra" "castrorum" "castris" neuter));
    casus_N = mkN "casus" "casus" masculine;
    catena_N = mkN "catena";
    causa_N = mkN "causa";
    causa_Prep = mkPostp "causa" Gen;
    cavare_V = mkV "cavare";
    cavere_V = mkV "cavere";
    cedere_V = mkV "cedere" "cedo" "cessi" "cessum";
    celare_V = mkV "celare";
    celer_A = mkA "celer" "celeris"; -- strange?
    celeritas_N = mkN "celeritas" "celeritatis" feminine;
    celeriter_Adv = ss "celeriter"; -- comparison? missing celerius, celerrime
    census_N = mkN "census" "census" masculine;
    censere_V = mkV "censere";
    centuriare_V = mkV "centuriare";
    centurio_N = mkN "centurio" "centurionis" masculine;
    cernere_V = mkV "cernere" "cerno" "crevi" "cretum";
    certare_V = mkV "certare";
    certamen_N = mkN "certamen" "certaminis" neuter;
    certus_A = mkA "certus";
    ceterus_A = mkA "ceterus";
    cibarius_A = mkA "cibarius";
    cibus_N = mkN "cibus";
    ciere_V = mkV "ciere" "cio" "civi" "citum";
    cingere_V = mkV "cingere" "cingo" "cingi" "cinctum";
    circinare_V = mkV "circinare";
    circinus_N = mkN "circinus";
    circiter_Adv = ss "circiter";
    circiter_Prep = mkPrep "circiter" Acc;
    circuitus_N = mkN "circuitus" "circuitus" masculine;
    circum_Adv = ss "circum";
    circum_Prep = mkPrep "circum" Acc;
    circumdare_V = mkV "circumdare" "circumdo" "circumdedi" "circumdatum"; -- prefixVerb "circum" dare_V; -- circum + dare, missing circumdederant, circumdederunt
    circumducere_V = mkV "circumducere" "circumduco" "circumduxi" "circumductum"; -- prefixVerb "circum" ducere_V; circum + ducere
    circumiectus_A = mkA "circumiectus";
    circumire_V = prefixVerb "circum" ire_V;
    circummunire_V = mkV "circummunire";
    circumsistere_1_V = mkV "circumsistere" "circumsisto" "circumstiti" "circumstatum" ; -- prefixVerb "circum" sistere_1_V; -- circum + sistere
--    circumsistere_2_V = prefixVerb "circum" sistere_2_V; -- circum + sistere
    circumvenire_V = mkV "circumvenire" ; -- prefixVerb "circum" venire_V; -- circum + venire
    cis_Prep = mkPrep "cis" Acc;
    citare_V = mkV "citare";
    citer_A = mkA "citer"; -- missing citeriore, citeriorem, citerioris
    citra_Adv = ss "citra";
    citus_A = mkA "citus";
    civitas_N = mkN "civitas" "civitatis" feminine;
    colere_V = mkV "colere" "colo" "colui" "cultum";
    cooriri_V = mkV "cooriri" "coorior" "coortus"; -- prefixVerb "con" oriri_V; -- con + oriri, missing coorta
    conferre_V = prefixVerb "con" ferre_V; -- con + ferre
  ---
    conspicere_V = mkV "conspicere" "conspicio" "conspexi" "conspectum"; -- prefixVerb "con" specere_V; -- con + specere
    conspirare_V = mkV "conspirare"; -- con + spirare?
    constanter_Adv = ss "constanter"; -- comparison
    constantia_N = mkN "constantia";
    constare_V = mkV "constare"; -- prefixVerb "con" stare_V; -- con + stare, missing constiterant, constiterat, constiterunt, constitissent, constitisset, constitit
--    consternare_V = mkV "consternare"; -- con + sternere ?
    consternere_V = mkV "consternere" "consterno" "constravi" "constratum"; -- con + sternere?
    constituere_V = mkV "constituere" "constituo" "constitui" "constitutum"; -- prefixVerb "con" statuere_V; -- con + statuere
    constitutum_N = mkN "constitutum";
    consuere_V = mkV "consuere" "consuo" "consui" "consustum";
    consuescere_V = mkV "consuescere" "consuesco" "consuevi" "consuetum"; -- con + suescere?, missing consuesse, consuessent?
    consuetudo_N = mkN "consuetudo" "consuetudinis" feminine;
    consul_N = mkN "consul" "consulis" masculine;
    consulatus_N = mkN "consulatus" "consulatus" masculine;
    consulere_V = mkV "consulere" "consulo" "consului" "consultum";
    consultare_V = mkV "consultare";
    consultum_N = mkN "consultum";
    contemptio_N = mkN "contemptio" "contemptionis" feminine;
    contemptus_A = mkA "contemptus";
    contemptus_N = mkN "contemptus" "contemptus" masculine;
    contentio_N = mkN "contentio" "contentionis" feminine;
    contendere_V = mkV "contendere" "contendo" "contendi" "contentum";
    contexere_V = mkV "contexere" "contexo" "contexui" "contextum"; -- prefixVerb "con" texere_V; -- con + texere
    continens_N = mkN "continens" "continentis" feminine;
    continenter_Adv = ss "continenter";
    continere_V2 = mkV2 (mkV "continere"); -- prefixVerb2 "con" tenere_V2; con + tenere
    contingere_V = mkV "contingere" "contingo" "contigi" "contectum"; -- con + tangere?
    continuatio_N = mkN "continuatio" "continuationis" feminine;
    continuus_A = mkA "continuus";
    contra_Adv = ss "contra";
--    contrahere_V2 = -- prefixVerb2 "con" trahere_V2; -- con + trahere
    contrarius_A = mkA "contrarius";
    contumelia_N = mkN "contumelia";
    convallis_N = mkN "convallis" "convallis" feminine;
    convenire_V = prefixVerb "con" venire_V; -- missing convenerant, convenerat, convenerunt, convenisse, convenissent, convenisset, conventu, conventus
    conversare_V = mkV "conversare";
    convertere_V = prefixVerb "con" vertere_V; -- con + vertere
    convincere_V = prefixVerb "con" vincere_V; -- con + vincere
    convocare_V = prefixVerb "con" vocare_V; -- con + vocare
    copia_N = mkN "copia";
    copiosus_A = mkA "copiosus";
    copula_N = mkN "copula";
    cora_N = mkN "cora";
    corona_N = mkN "corona";
    corpus_N = mkN "corpus" "corporis" neuter;
    cos_N = mkN "cos" "cotis" feminine;
    cotidianus_A = mkA "cotidianus";
    cotidie_Adv = ss "cotidie";
    Cotta_PN = mkPN (lin N (singularN (mkN "Cotta")));
    crassitudo_N = mkN "crassitudo" "crassitudinis" feminine;
    Crassus_PN = mkPN (lin N (singularN (mkN "Crassus")));
    cratis_N = mkN "cratis" "cratis" feminine;
    creare_V = mkV "creare";
    creber_A = mkA "creber";
    credere_V = mkV "credere" "credo" "credidi" "creditum";
    cremare_V = mkV "cremare";
    crescere_V = mkV "crescere" "cresco" "crevi" "cretum";
    Creta_N = mkN "Creta";
    cruciare_V = mkV "cruciare";
    cruciatus_N = mkN "cruciatus" "cruciatus" masculine;
    crudelitas_N = mkN "crudelitas" "crudelitatis" feminine;
    crudeliter_Adv = ss "crudeliter"; -- comparison?
    culmen_N = mkN "culmen" "culminis" neuter;
    culpa_N = mkN "culpa";
    cultura_N = mkN "cultura";
    cultus_N = mkN "cultus" "cultus" masculine;
    cum_Prep = mkPrep "cum" Abl;
    cunctari_V = mkV "cunctari";
    cunctatio_N = mkN "cunctatio" "cunctationis" feminine;
    cunctus_A = mkA "cunctus";
    cuniculus_N = mkN "cuniculus";
    cupere_V = mkV "cupere" "cupio" "cupivi" "cupitum";
    cupiditas_N = mkN "cupiditas" "cupiditatis" feminine;
    cupidus_A = mkA "cupidus";
    cur_Adv = ss "cur";
    cura_N = mkN "cura";
    curare_V = mkV "curare"; -- missing curasset
    currere_V = mkV "currere" "curro" "cucurri" "cursum";
    currus_N = mkN "currus" "currus" masculine;
    custodia_N = mkN "custodia";
    damnare_V = mkV "damnare";
    damnatus_A = mkA "damnatus";
    dare_V = mkV "dare" "do" "dedi" "datum";
    datum_N = mkN "datum";
    de_Prep = mkPrep "de" Abl;
    debere_VV = StructuralLat.must_VV;
    ducere_V = mkV "ducere" "duco" "duxi" "ductum" ;
    equitare_V = mkV "equitare";
    ferre_V = fixFerre (mkVerb "ferre" "fer" "fer" "fera" "fereba" "ferre" "fere" "fer" "tul" "tul" "tuleri" "tulera" "tulisse" "tuleri" "lat");
    iacere_V = mkV "iacere" "iacio" "ieci" "iactum";
    ire_V = LexiconLat.go_V;
--    ne_an_Conj = mkConj (BIND ++ "ne") "an" Sg;
--    nonne_an_Conj = mkConj "nonne" "an" Sg;
--    num_an_Conj = mkConj "num" "an" Sg;
    oriri_V = mkV "oriri" "orior" nonExist "ortus";
    qui_IP = StructuralLat.whatSg_IP;
    sistere_1_V = mkV "sistere" "sisto" "stiti" "statum";
    sistere_2_V = mkV "sistere" "sisto" "steti" "statum";
    specere_V = mkV "specere" "speco" "spexi" "spectum";
    stare_V = LexiconLat.stand_V;
    statuere_V = mkV "statuere" "statuo" "statui" "statutum";
    tenere_V2 =  LexiconLat.hold_V2;
    texere_V = mkV "texere" "texo" "texui" "textum";
    trahere_V2 = LexiconLat.pull_V2;
--    utrum_an_Conj = mkConj "utrum" "an" Sg;
    venire_V = LexiconLat.come_V;
    vertere_V = mkV "vertere" "verto" "verti" "versum";
    vincere_V = mkV "vincere" "vinco" "vici" "victum";
    vocare_V = mkV "vocare";
  oper
    fixFerre : Verb -> Verb =
      \ferre ->
      {
  	act = table
  	  {
  	    (VAct VSim (VPres VInd) Sg P2) => "fers";
	    (VAct VSim (VPres VInd) Sg P3) => "fert";
	    (VAct VSim (VPres VInd) Pl P1) => "ferimus";
	    (VAct VSim (VPres VInd) Pl P2) => "fertis";
  	    rest => ferre.act ! rest
  	  };
	ger = ferre.ger;
	geriv = ferre.geriv;
	imp = table
	  {
	    (VImp1 Sg) => "fer";
	    (VImp1 Pl) => "ferte";
	    (VImp2 Sg P2) => "ferto";
	    (VImp2 Sg P3) => "ferto";
	    (VImp2 Pl P2) => "fertote";
	    rest => ferre.imp ! rest
	  };
	inf = ferre.inf;
	part = ferre.part;
	pass = table
	  {
	    VPass (VPres VInd) Sg P2 => "ferris";
	    VPass (VPres VInd) Sg P3 => "fertur";
	    rest => ferre.pass ! rest
	  };
	sup = ferre.sup;
	  
	  
      } ;
}