--# -path=.:abstract:common
concrete LexiconRus of Lexicon = CatRus ** 
  open ParadigmsRus, Prelude, StructuralRus, MorphoRus, (E = ExtraRus) in {
flags 
  optimize=values ;
  coding=utf8 ;
lin
  add_V3 = mkV3 (regV imperfective first "складыва" "ю" "складывал" "складывай" "складывать" ) "" "в" accusative accusative;
  airplane_N = mkN "самолёт" ;
  already_Adv = mkAdv "уже" ;
  animal_N = mkN "животное" animate;
  answer_V2S = dirV2 (regV imperfective first "отвеча" "ю" "отвечал" "отвечай" "отвечать" );
  apartment_N = mkN "квартира" ;
  apple_N = mkN "яблоко" inanimate ;
  art_N = mkN "искусство" ;
  ashes_N = mkN "пепел" ;
  ask_V2Q = dirV2 (regV imperfective first "спрашива" "ю" "спрашивал" "спрашивай" "спрашивать") ;
  baby_N = mkN "малыш" animate;
  back_N = mkN "спина" ;
  bad_A = mkA "плохой" "хуже";
  bank_N = mkN "банк" ;
  bark_N = mkN "кора";
  beautiful_A = mkA "красивый";
  become_VA = regV perfective secondA "станов" "лю" "стал" "стань" "стать" ;
  beer_N = mkIndeclinableNoun "пиво" neuter inanimate ;
  beg_V2V = dirV2 (mkV imperfective "прошу" "просишь" "просит" "просим" "просите" "просят" "просил" "проси" "просить" );
  belly_N = mkN "живот" ;
  big_A = mkA "большой" "больше" ;
  bike_N = mkN "велосипед" ;
  bird_N = mkN "птица" animate;
  bite_V2 = dirV2 (regV imperfective first "куса" "ю" "кусал" "кусай" "кусать");
  black_A = mkA "чёрный";
  blood_N = mkN "кровь" ;
  blow_V = regV imperfective first "ду" "ю" "дул" "дуй" "дуть" ;
  blue_A = mkA "голубой" ;
  boat_N = mkN "лодка" ;
  bone_N = mkN "кость" ;
  book_N = mkN "книга" ;
  boot_N = mkN "сапог" ;
  boss_N = mkN "начальник" animate;
  boy_N = mkN "мальчик" animate;
  bread_N = mkN "хлеб" ;
  break_V2 = dirV2 (regV imperfective first "прерыва" "ю" "прерывал" "прерывай" "прерывать" );
  breast_N = mkN "грудь" ;
  breathe_V = regV imperfective second "дыш" "у" "дышал" "дыши" "дышать" ;
  broad_A = mkA "широкий" "шире";
  brother_N2 = mkN2 (mkN "брат" animate) ; -- FIXME: special case
  brown_A = mkA "коричневый";
  burn_V = regV imperfective second "гор" "ю" "горел" "гори" "гореть" ;
  butter_N = mkN "масло";
  buy_V2 = dirV2 (regV imperfective first "покупа" "ю" "покупал" "покупай" "покупать" );
  camera_N = mkN "фотоаппарат" ;
  cap_N = mkN "чашка" ; -- vowel change
  car_N = mkN "машина" ;
  carpet_N = mkN "ковёр"; -- vowel change
  cat_N = mkN "кошка" animate ; -- vowel change
  ceiling_N = mkN "потолок" ; -- vowel change
  chair_N = mkN "стул" ; -- irregular
  cheese_N = mkN "сыр" ;
  child_N = mkNAltPl "ребёнок" "деть" masculine animate;
--  child_N = mkN "ребёнок" "ребёнка" "ребёнку" "ребёнка" "ребёнком" "ребёнке" "ребёнке" "дети" "детей" "детям" "детей" "детьми" "детях"  masculine animate ;
  church_N = mkN "церковь" "церкви" "церкви" "церковь" "церковью" "церкви" "церкви" "церкви" "церквей" "церквям" "церкви" "церквями" "церквях"  masculine inanimate ;
  city_N = mkN "город" ;
  clean_A = mkA "чистый" "чище"; 
  clever_A = mkA "умный";
  close_V2= dirV2 (regV imperfective first "закрыва" "ю" "закрывал" "закрывай" "закрывать" );
  cloud_N = mkN "облако" ; -- irregular
  coat_N = mkIndeclinableNoun "пальто" masculine inanimate ;
  cold_A = mkA "холодный";
  come_V = regV imperfective first "прихо" "жу" "приходил" "приходи" "приходить" ;
  computer_N = mkN "компьютер" ;
  correct_A = mkA "правильный" ; 
  count_V2 = dirV2 (regV imperfective first "счита" "ю" "считал" "считай" "считать" ) ;
  country_N = mkN "страна" ;
  cousin_N = mkN "кузен" ; -- FIXME: is this really correct? can't find it in the dictionary
  cow_N = mkN "корова" animate ;
  cut_V2 = dirV2 (regV imperfective first "реж" "у" "резал" "режь" "резать" ) ;
  day_N = mkN "день" "дня" "дню" "день" "днём" "дне" "дне" "дни" "дней" "дням" "дни" "днями" "днях" masculine inanimate ;
  die_V = regV imperfective first "умира" "ю" "умирал" "умирай" "умирать" ;
  dig_V = regV imperfective first "копа" "ю" "копал" "копай" "копать" ;
  dirty_A = mkA "грязный" ;
  distance_N3 = mkN3 (mkN "расстояние") from_Prep to_Prep ;
  do_V2 = dirV2 (regV imperfective first "дела" "ю" "делал" "делай" "делать" );
  doctor_N = mkN "доктор" animate ;
  dog_N = mkN "собака" animate;
  door_N = mkN "дверь" ;
  drink_V2 = dirV2 (regV imperfective firstE "пь" "ю" "пил" "пей" "пить" );
  dry_A = mkA "сухой" "суше";
  dull_A = mkA "скучный" ;
  dust_N = mkN "пыль" ;
  ear_N = mkN "ухо" ;
  earth_N = mkN "земля" ;
  easy_A2V = mkA2 (mkA "лёгкий" "легче") "для" genitive ;
  eat_V2 = dirV2 (regV imperfective first "куша" "ю" "кушал" "кушай" "кушать" );
  egg_N = mkN "яйцо" ;
  empty_A = mkA "пустой" ;
  enemy_N = mkN "враг" animate ;
  eye_N = mkN "глаз" ; -- FIXME: Pl -a
  factory_N = mkN "фабрика" ;
  fall_V = regV imperfective first "пада" "ю" "падал" "падай" "падать" ;
  far_Adv = mkAdv "далеко";
  fat_N = mkN "жир" ;
  father_N2 = mkN2 (mkN "отец" "отца" "отцу" "отца" "отцом" "отце" "отце" "отцы" "отцов" "отцам" "отцов" "отцами" "отцах" masculine animate);
  fear_V2 =dirV2 (regV imperfective first "бо" "ю" "боял" "бой" "боять" );
  fear_VS = regV imperfective second "бо" "ю" "боял" "бой" "боять" ;
  feather_N = mkN "перо" "пера" "перу" "пера" "пером" "пере" "пере" "перья" "перьев" "перьям" "перьев" "перьями" "перьях" neuter inanimate ;
  fight_V2 = dirV2 (regV imperfective firstE "дер" "у" "драл" "дери" "драть" ) ;
  find_V2 = dirV2 (mkV imperfective "нахожу" "находишь" "находит" "находим" "находите" "находят" "находил" "находи" "находить" );
  fingernail_N = mkN "ноготь" "ногтя" "ногтю" "ногтя" "ногтем" "ногте" "ногте" "ногти" "ногтей" "ногтям" "ногтей" "ногтями" "ногтях"  masculine inanimate ;
  fire_N = mkN "огонь" "огня" "огню" "огня" "огнём" "огне" "огне" "огни" "огней" "огням" "огней" "огнями" "огнях" masculine inanimate ;
  fish_N = mkN "рыба" animate;
  float_V = regV imperfective firstE "плыв" "у" "плыл" "плыви" "плыть" ;
  floor_N = mkN "пол" ;
  flow_V = regV imperfective firstE "тек" "у" "тёк" "теки" "течь" ;
  flower_N = mkN "цветок";
  fly_V = regV imperfective first "лета" "ю" "летал" "летай" "летать" ;
  fog_N = mkN "туман" ;
  foot_N = mkN "ступня" ;
  forest_N = mkN "лес" ; -- prepos -u
  forget_V2= dirV2 (regV imperfective first "забыва" "ю" "забывал" "забывай" "забывать" );
  freeze_V = regV imperfective first "замерза" "ю" "замерзал" "замерзай" "замерзать" ;
  fridge_N = mkN "холодильник" ;
  friend_N = mkN "друг" "друга" "другу" "друга" "другом" "друге" "друге" "друзья" "друзей" "друзьям" "друзей" "дузьями" "друзьях" masculine animate ;
  fruit_N = mkN "фрукт" ;
  full_A = mkA "полный";
  fun_AV = mkA "весёлый";
  garden_N = mkN "сад" ;
  girl_N = mkN "девочка" animate; -- vowel change
  give_V3 = tvDirDir (regV imperfective firstE "да" "ю" "давал" "давай" "давать" ) ;
  glove_N = mkN "перчатка" ; -- vowel change
  go_V = mkV imperfective "хожу" "ходишь" "ходит" "ходим" "ходите" "ходят" "ходил" "ходи" "ходить" ;
  gold_N = mkN "золото" ;
  good_A = mkA "хороший" "лучше" ; 
  grammar_N = mkN "грамматика";
  grass_N = mkN "трава";
  green_A = mkA "зелёный" ;
  guts_N = mkN "внутренность" ;
  hair_N = mkN "волос" ; -- FIXME: always plural?
  hand_N = mkN "рука" ;
  harbour_N = mkN "порт" ; -- prepos -u
  hat_N = mkN "шляпа" ;
  hate_V2= dirV2 (mkV imperfective "ненавижу" "ненавидишь" "ненавидит" "ненавидим" "ненавидите" "ненавидят" "ненавидел" "ненавидь" "ненавидеть" );
  head_N = mkN "голова" ;
  hear_V2= dirV2 (regV imperfective first "слуша" "ю" "слушал" "слушай" "слушать" );
  heart_N = mkN "сердце" "сердца" "сердцу" "сердца" "сердцем" "сердце" "сердце" "сердца" "сердец" "сердцам" "сердец" "сердцами" "сердцах"  neuter inanimate ;
  heavy_A = mkA "тяжёлый" ;
  hill_N = mkN "холм" ;
  hit_V2 = dirV2 (regV imperfective first "ударя" "ю" "ударял" "ударяй" "ударять" );
  hold_V2 = dirV2 (regV imperfective second "держ" "у" "держал" "держи" "держать" );
  hope_VS= regV imperfective first "наде" "ю" "надеял" "надей" "надеять" ;
  horn_N = mkN "рог" ;
  horse_N = mkN "лошадь" animate; -- irregular
  hot_A = mkA "горячий" ;
  house_N = mkN "дом" ;
  hunt_V2 = dirV2 (regV imperfective second "охоч" "у" "охотил" "охоть" "охотить" ) ;
  husband_N = mkN "муж" "мужа" "мужу" "мужа" "мужем" "муже" "муже" "мужья" "мужей" "мужьям" "мужей" "мужьями" "мужьях" masculine animate ;
  ice_N = mkN "лёд" "льда" "льду" "льда" "льдом" "льде" "льде" "льды" "льдов" "льдам" "льдов" "льдами" "льдах" masculine inanimate ;
  important_A = mkA "важный" ;
  industry_N = mkN "промышленность" ; 
  iron_N = mkN "железо" ;
  john_PN = mkPN "Иван" Masc Sg Animate ;
  jump_V = regV imperfective first "прыга" "ю" "прыгал" "прыгай" "прыгать" ;
  kill_V2 = dirV2 (regV imperfective first "убива" "ю" "убивал" "убивай" "убивать" ) ;
  king_N = mkN "король" "короля" "королю" "короля" "королем" "короле" "короле" "короли" "королей" "королям" "королей" "королями" "королях"  masculine animate ;
  knee_N = mkN "колено" "колена" "колену" "колена" "коленом" "колене" "колене" "колени" "колен" "коленам" "колен" "коленями" "коленях"  neuter inanimate ;
  know_V2= dirV2 (regV imperfective first "зна" "ю" "знал" "знай" "знать" );
  know_VS= mkVQ (regV imperfective first "зна" "ю" "знал" "знай" "знать" );
  know_VQ= mkVQ (regV imperfective first "зна" "ю" "знал" "знай" "знать" );
  lake_N = mkN "озеро" ; -- gen pl "озёр"
  lamp_N = mkN "лампа" ;
  language_N = mkN "язык" ;
  laugh_V = regV imperfective firstE "сме" "ю" "смеял" "смей" "смеять" ;
  leaf_N = mkN "лист" ; -- irregular pl
  learn_V2= dirV2 (regV imperfective second "уч" "у" "учил" "учи" "учить" );
  leather_N = mkN "кожа" ;
  leave_V2= dirV2 (mkV imperfective "ухожу" "уходишь" "уходит" "уходим" "уходите" "уходят" "уходил" "уходи" "уходить" );
  left_Ord = (uy_j_EndDecl "лев" ) ** {lock_A = <>}; 
  leg_N = mkN "нога" ;
  lie_V = regV imperfective firstE "лг" "у" "лгал" "лги" "лгать" ;
  like_V2= dirV2 (regV imperfective second "нрав" "лю" "нравил" "нравь" "нравить" );
  listen_V2= dirV2 (regV imperfective first "слуша" "ю" "слушал" "слушай" "слушать" );
  live_V= regV imperfective firstE "жив" "у" "жил" "живи" "жить" ;
  liver_N = mkN "печень" ;
  long_A = mkA "длинный" ;
  lose_V2 = dirV2 (regV imperfective first "теря" "ю" "терял" "теряй" "терять" );
  louse_N = mkN "вошь" "вши" "вши" "вошь" "вошью" "вше" "вше" "вши" "вшей" "вшам" "вшей" "вшами" "вшах" feminine animate ;
  love_N = mkN "любовь" ; -- vowel change
  love_V2= dirV2 (regV imperfective second "люб" "лю" "любил" "люби" "любить" );
  man_N = mkNAltPl "человек" "людь" masculine animate ; -- null gen pl
  married_A2 = mkA2 (mkA "замужем") "за" instructive ;
  meat_N = mkN "мясо" ;
  milk_N = mkN "молоко" ;
  moon_N = mkN "луна" ;
  mother_N2 = mkN2 (mkN "мать" "матери" "матери" "мать" "матерью" "матери" "матери" "матери" "матерей" "матерям" "матерей" "матерями" "матерях" feminine animate) ;
  mountain_N = mkN "гора" ;
  mouth_N = mkN "рот" "рта" "рту" "рот" "ртом" "рте" "рте" "рты" "ртов" "ртам" "рты" "ртами" "ртах" masculine inanimate ;
  music_N = mkN "музыка" ;
  name_N = mkN "имя" ;
  narrow_A = mkA "узкий" "уже" ;
  near_A = mkA "близкий" "ближе";
  neck_N = mkN "шея" ;
  new_A = mkA "новый" ;
  newspaper_N = mkN "газета" ;
  night_N = mkN "ночь" ;
  nose_N = mkN "нос" ;
  now_Adv = mkAdv "сейчас" ;
  number_N = mkN "число" ; -- gen pl "чисел"
  oil_N = mkN "нефть" ;
  old_A = mkA "старый" "старше" ;
  open_V2= dirV2 (regV imperfective first "открыва" "ю" "открывал" "открывай" "открывать" );
---  organise_V2 = dirV2 (regV imperfective foreign "организу" "ю" "организовал" "организуй" "организовать" ); -- +++ MG_UR: added +++
  paint_V2A = dirV2 (regV imperfective first "рису" "ю" "рисовал" "рисуй" "рисовать" ) ;
---  palace_N = nDvorec "двор" ; -- +++ MG_UR: added +++
  paper_N = mkN "бумага" ;
  paris_PN = mkPN "Париж" Masc Sg Inanimate ;
  peace_N = mkN "мир" ;
  pen_N = mkN "ручка" ;
  person_N = mkN "лицo" animate ; -- irregular
  planet_N = mkN "планета" ;
  plastic_N = mkN "пластмасса" ;
  play_V = regV imperfective first "игра" "ю" "играл" "играй" "играть" ;
  play_V2 = mkV2 (regV imperfective first "игра" "ю" "играл" "играй" "играть" ) "c" instructive;
  policeman_N = mkN "милиционер" animate ;
  priest_N = mkN "священник" animate;
  probable_AS = mkA "возможный" ;
  pull_V2 = dirV2 (regV imperfective first "тян" "у" "тянул" "тяни" "тянуть" ) ;
  push_V2 = dirV2 (regV imperfective first "толка" "ю" "толкал" "толкай" "толкать" );
  put_V2 = dirV2 (regV imperfective firstE "клад" "у" "клал" "клади" "класть" );
  queen_N = mkN "королева" animate ;
  question_N = mkN "вопрос" ;
  radio_N = mkIndeclinableNoun "радио" neuter inanimate;
  rain_N = mkN "дождь" ;
  rain_V0 = idetDozhd verbIdti; -- No such verb in Russian!
  read_V2 = dirV2 (regV imperfective first "чита" "ю" "читал" "читай" "читать" );
-- ready_A = ;
  reason_N = mkN "причина";
  red_A = mkA "красный" ;
  religion_N = mkN "религия" ;
  restaurant_N = mkN "ресторан" ;
  right_Ord = (uy_j_EndDecl "прав") ** {lock_A = <>} ;
  river_N = mkN "рекa" ;
  road_N = mkN "дорогa" ;
  rock_N = mkN "камень" ;
  roof_N = mkN "крыша" ;
  root_N = mkN "корень" ;
  rope_N = mkN "верёвка" ;
  rotten_A = mkA "гнилой";
  round_A = mkA "круглый";
  rub_V2 = dirV2 (regV imperfective firstE "тр" "у" "тёр" "три" "тереть" );
  rubber_N = mkN "резина" ;
  rule_N = mkN "правило" ;
  run_V = regV imperfective first "бега" "ю" "бегал" "бегай" "бегать" ;
  salt_N = mkN "соль" ;
  sand_N = mkN "песок" "песка" "песку" "песок" "песком" "песке" "песке" "пески" "песков" "пескам" "песков" "песками" "песках"  masculine inanimate ;
  say_VS = regV imperfective second "говор" "ю" "говорил" "говори" "говорить" ;
  school_N = mkN "школа" ;
  science_N = mkN "наука" ;
  scratch_V2 = dirV2 (regV imperfective first "чеш" "у" "чесал" "чеши" "чесать" ) ; 
  sea_N = mkN "море" ;
  see_V2 = dirV2 (mkV imperfective "вижу" "видишь" "видит" "видим" "видите" "видят" "видел" "видь" "видеть");
  seed_N = mkN "семя";
  seek_V2 = dirV2 (regV imperfective first "ищ" "у" "искал" "ищи" "искать" );
  sell_V3 = tvDirDir (regV imperfective firstE "прода" "ю" "продавал" "продавай" "продавать" );
  send_V3 = tvDirDir (regV imperfective first "посыла" "ю" "посылал" "посылай" "посылать" );
  sew_V = regV imperfective firstE "шь" "ю" "шил" "шей" "шить" ;
  sharp_A = mkA "острый";
  sheep_N = mkN "овца" animate ;
  ship_N = mkN "корабль" ;
  shirt_N = mkN "рубашка" ;
  shoe_N = mkN "туфля" "туфли" "туфле" "туфлю" "туфлей" "туфле" "туфле" "туфли" "туфель" "туфлям" "туфли" "туфлями" "туфлях"  masculine inanimate ;
  shop_N = mkN "магазин" ;
  short_A = mkA "короткий" "короче" ;
  silver_N = mkN "серебро" ;
  sing_V = regV imperfective firstE "по" "ю" "пел" "пой" "петь" ;
  sister_N = mkN "сестра" animate ;
  sit_V = mkV imperfective "сижу" "сидишь" "сидит" "сидим" "сидите" "сидят" "сидел" "сиди" "сидеть" ;
  skin_N = mkN "кожа" ;
  sky_N = mkN "небо" "неба" "небу" "небо" "небом" "небе" "небе" "небеса" "небес" "небесам" "небес" "небесами" "небесах" neuter inanimate ;
  sleep_V = regV imperfective second "сп" "лю" "спал" "спи" "спать" ;
  small_A = mkA "маленький" "меньше" ;
  smell_V = regV imperfective first "пахн" "у" "пахнул" "пахни" "пахнуть" ;
  smoke_N = mkN "дым" ;
  smooth_A = mkA "гладкий" "глаже";
  snake_N = mkN "змея" animate ;
  snow_N = mkN "снег" ;
  sock_N = mkN "носок" ;
  song_N = mkN "песня" ;
  speak_V2 = mkV2 (regV imperfective secondA "говор" "ю" "говорил" "говори" "говорить")
               "на" prepositional ;
  spit_V = regV imperfective firstE "плю" "ю" "плевал" "плюй" "плевать" ;
  split_V2 = dirV2 (regV imperfective first "разбива" "ю" "разбивал" "разбей" "разбивать" ) ;
  squeeze_V2 = dirV2 (regV imperfective first "сжима" "ю" "сжимал" "сжимай" "сжимать" ) ;
  stab_V2 = dirV2 (regV imperfective first "кол" "ю" "колол" "коли" "колоть" ) ;
  stand_V = regV imperfective second "сто" "ю" "стоял" "стой" "стоять" ;
  star_N = mkN "звезда" ;
  steel_N = mkN "сталь" ;
  stick_N = mkN "палка" ;
  stone_N = mkN "камень" ;
  stop_V = regV imperfective first "останавлива" "ю" "останавливал" "останавливай" "останавливать";
  stove_N = mkN "печь" ;
  straight_A = mkA "прямой" ;
  student_N = mkN "студент" animate ;
  stupid_A = mkA "тупой" "тупее" ;
  suck_V2 = dirV2 (regV imperfective firstE "сос" "у" "сосал" "соси" "сосать") ;
  sun_N = mkN "солнце" "солнца" "солнцу" "солнце" "солнцем" "солнце" "солнце" "солнца" "солнц" "солнцам" "солнца" "солнцами" "солнцах"  neuter inanimate ;
  swell_V = regV imperfective first "опуха" "ю" "опухал" "опухай" "опухать" ;
  swim_V = regV imperfective first "плава" "ю" "плавал" "плавай" "плавать" ;
  switch8off_V2 = dirV2 (regV imperfective first "выключа" "ю" "выключал" "выключай" "выключать") ;
  switch8on_V2 = dirV2 (regV imperfective first "включа" "ю" "включал" "включай" "включать") ;
  table_N = mkN "стол" ;
  tail_N = mkN "хвост" ;
  talk_V3 = mkV3 (regV imperfective second "говор" "ю" "говорил" "говори" "говорить" ) "с" "о" instructive prepositional;
  teach_V2 = dirV2 (regV imperfective second "уч" "у" "учил" "учи" "учить" );
  teacher_N = mkN "учитель" animate ;
  television_N = mkN "телевидение" ; -- FIXME: televizor?
  thick_A = mkA "толстый" "толще" ;
  thin_A = mkA "тонкий" "тоньше" ;
  think_V = regV imperfective first "дума" "ю" "думал" "думай" "думать" ;
  throw_V2 = dirV2 (regV imperfective first "броса" "ю" "бросал" "бросай" "бросать" ) ;
  tie_V2 = dirV2 (regV imperfective first "вяж" "у" "вязал" "вяжи" "вязать") ;
  today_Adv = mkAdv "сегодня" ;
  tongue_N = mkN "язык" ;
  tooth_N = mkN "зуб" ;
  train_N = mkN "поезд" ;
  travel_V = regV imperfective first "путешеству" "ю" "путешествовал" "путешествуй" "путешествовать" ;
  tree_N = mkN "дерево" ; -- irregular
  turn_V = regV imperfective first "поворачива" "ю" "поворачивал" "поворачивай" "поворачивать" ;
  ugly_A = mkA "некрасивый" ;
--  uncertain_A = ;
  understand_V2 = dirV2 (regV imperfective first "понима" "ю" "понимал" "понимай" "понимать" );
  university_N = mkN "университет" ;
  village_N = mkN "деревня" ;
  vomit_V = regV imperfective firstE "рв" "у" "рвал" "рви" "рвать" ;
  wait_V2 = dirV2 (regV imperfective firstE "жд" "у" "ждал" "жди" "ждать" );
  walk_V = regV imperfective first "гуля" "ю" "гулял" "гуляй" "гулять" ;
---  want_V2 = dirV2 (regV imperfective mixed "хо" "чу" "хотел" "хоти" "хотеть" );
  war_N = mkN "война" ;
  warm_A = mkA "тёплый" ;
  wash_V2 = dirV2 (regV imperfective first "мо" "ю" "мыл" "мой" "мыть" ) ;
  watch_V2 = dirV2 (regV imperfective second "смотр" "ю" "смотрел" "смотри" "смотреть" );
  water_N = mkN "вода" ;
  wet_A = mkA "мокрый" ;
  white_A = mkA "белый" ;
  wide_A = mkA "широкий" "шире";
  wife_N = mkN "жена" animate ;
  win_V2 = dirV2 (regV imperfective first "выигрыва" "ю" "выигрывал" "выигрывай" "выигрывать" );
  wind_N = mkN "ветер" "ветра" "ветру" "ветер" "ветром" "ветра" "ветра" "ветров" "ветра" "ветрам" "ветров" "ветрами" "ветрах" masculine inanimate ;
  window_N = mkN "окно" ; -- "окон" 
  wine_N = mkN "вино" ; 
  wing_N = mkN "крыло" ; -- pl крылья крыльев etc
  wipe_V2 = dirV2 (regV imperfective first "вытира" "ю" "вытирал" "вытирай" "вытирать" );
  woman_N = mkN "женщина" ;
  wonder_VQ = regV imperfective first "интересу" "ю" "интересовал" "интересуй" "интересовать"; 
  wood_N = mkN "дерево" ;
  worm_N = mkN "черв" ;
  write_V2 = dirV2 (regV imperfective first "пиш" "у" "писал" "пиши" "писать" );
  year_N = mkNAltPl "год" "лето" masculine inanimate ;
  yellow_A = mkA "жёлтый" ;
  young_A = mkA "молодой" "моложе" ;
}
