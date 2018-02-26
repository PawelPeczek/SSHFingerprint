;---------------------------------------------------------------------------------------------------------------------------------------
;|															Czesc deklaracyjna														   |
;---------------------------------------------------------------------------------------------------------------------------------------

data1 segment
	
	ArgTab		db	128 dup(24h)	;	Wypełnienie tablicy argumentow pobranych z lini polecen samymi znakami "$" -  w skutek czego  
									;	nie trzeba juz dodawać na koncu ciagu tego znaku. Maksymalnie przyjmuje 127 znakow + dolar 
									;	terminujacy - tyle przyjmuje maksymalnie od adresu PSP:81h do PSP:FFh
	ArgStrLen 	db	0				;	Dlugosc ciagu znakow przekazanego do wiersza polecenia jako argument
	ArgNumber	db 	0				;	Ilosc argumentow
	ArgOffsets	db	64 dup(0)		;	Tablica (maksymalnie 64 argumenty, bo gdyby przekazac arg1 arg2 ... to liczba argumentow 
									;	maksymalnie wyniesie 64 - kazdy argument po 1 znak (1B ASCII) + odstep, np spacja 20h 
									;	ASCII - 1B) - okreslenie przesuniecia wzgledem poczatku tablicy
	endl		db	10,13,"$"
	reqNumArg	db	2
	SSHkey		db	16 dup(?)		;	Przekonwertowany na postac binarna skrot klucza publicznego SSH
	errorMsgOff	dw 	offset statusOK	;	Przechowuje offset do wiadomosci, ktora ma sie wyswietlic (status wykonania)
	corrupChar	db	1 dup(33)		;	Przechowuje	pozycje zlych cyfr szesnastkowych
	corCharTxt	db	3 dup("$")
	d 			db	10
	pos 		db	33 dup("$")
	hex 		db	16d
	ASCIIArtTab	db	9 dup(7Ch, 17 dup(0d), 7Ch, 10, 13), "$"
	binMask		db	00000011b
	actFigPos	db 	93d
	divider		db 	21d
	line		db 	"+-----------------+", 10, 13, "$"
	translate	db 	20h, 2Eh, 0F8h, 2Bh, 3Dh, 2Ah, 42h, 4Fh, 58h, 40h, 25h, 26h, 23h, 2Fh, 5Eh 	;	Tablica konwersji znaków

	;--------------------------------
	;|		Wiadomosci zwrotne		|
	;--------------------------------

	corCharEx	db	"W podanym skrocie klucza SSH wystapil blad. Znak na nastepujacej pozycji wymaga poprawy na zestaw [0-9a-f]: $"
	toFewArgEx	db	"Skladnia polecenia: sshfingerprint.exe mode SSH_key", 10, 13, "mode: 0 - normal; 1 - extended", 10, 13,
					"SSH_key - poprawny skrot klucza SSH$"
	toManyArgEx	db	"[WARNING!] Podano zbyt duzo argumentow - program zignorowal nadmiarowe.$"
	statusOK 	db	"Status wykonania: [OK!]$"
	secArgEx	db	"Poprawna wartosc 1. argumentu to 0 lub 1$"
	nonExiArgEx	db	"Proba odwolania sie do nieistniejacego argumentu$"
	InvSSHLenEx	db	"Drugi argument ma nieodpowiednia dlugosc - oczekiwany jest skrot klucza SSH - 32 cyfr HEX", 10, 13, "$"


data1 ends

;---------------------------------------------------------------------------------------------------------------------------------------
;|													   Czesc deklaracyjna - KONIEC													   |
;---------------------------------------------------------------------------------------------------------------------------------------


;---------------------------------------------------------------------------------------------------------------------------------------
;|																SEGMENT KODU														   |
;---------------------------------------------------------------------------------------------------------------------------------------

code1 segment
	assume CS:code1, DS:data1, SS:stack1 		;	INFORMUJE kompilator do ktorego rej. ma sie odwolywac gdy napotka podana etykiete
	.286										;	Dla ułatwienia - pusha/popa dzieki czemu jedno polecenie odklada/zdejmuje wszystkie 
												;	rejestry na/ze stos/-u
	
	start:

			;	Inicjalizacja stosu
			mov AX, seg stack1
			mov SS, AX
			mov SP, offset top
			;	Koniec inicjalizacji

			; Inicjalizacja DS, aby wskazywal na segment data1
			mov AX, seg data1
			mov DS, AX
			

			;--------------------------------------------------------------------------------
			;	Punkt wejscia
			;--------------------------------------------------------------------------------
			
			main:

			call ParseArguments
			call ValidateArgs

			call AnalizeSSHKey
			call PrintChart
			call Terminate
		
			;--------------------------------------------------------------------------------
			;	KONIEC WYKONANIA
			;--------------------------------------------------------------------------------

	
	;----------------------------------------------------------------------------------------------------------------
	;
	;	Procedura ParseArguments
	;	Wykonuje parsowanie argumentow
	; 	Sparsowane argumenty umieszcza w tablicy ArgTab
	;	IN: 	none
	;	OUT: 	none
	;	DESC:	Procedura wlasciwa sparsowania argumentow. Najpierw zabezpieczane sa wartosci rejestrow. Nastepnie 
	;			wywolywana jest funkcja 51h przerwania 21h, ktora powoduje zaladowanie do BX segmentu PSP. wartosc
	;			jest kopiowana do rejestru segmentowego ES. Nastepnie pobierana jest do AL dlugosc przekazanych
	;			(wraz z poczatkowa spacja) z adresu PSP:[80h]. Jezeli nie podano zadnych argumentow - Wywolanie
	;			procedury Terminate. Nastepnie ustawiana jest wlasciwa dlugosc parametrow w pamieci (ArgStrLen)
	;			i ustawiony zostaje licznik petli na ta dlugosc. Rejestr indeksowy SI bedzie odpowiadal za wskazanie
	;			kolejnego znaku ES:SI (PSP:SI) od wartosci SI 82h - pominiecie spacji. DI - wskaze miejsce do kopiowania
	;			DS:SI, gdzie DS to tak naprawde segment ArgTab. Przy okazji DS:BX bedzie wskazywac kolejne komorki
	;			tablicy ArgOffsets - gdzie beda dlugosci poszczegolnych argumentow. W petli reading przechodzimy po
	;			wzsystkich znakach - wywolujac na kazdym procedure HandleCharacter. Po zakonzeniu petli musimy
	; 			wstawic znak terminujacy $ na koncu ostatniego argumentu i okreslic prawidlowo jego dlugosc.
	; 
	;----------------------------------------------------------------------------------------------------------------


	ParseArguments proc
		
		pusha

		mov AH, 51h
		int 21h						;	Wywolanie przerwania celem ustalenia PSP w BX
		mov AX, BX
		mov ES, AX 					;	Unikam przekazania nie z AX do rejestru segmentowego	
		mov AL, byte ptr ES:[80h]	;	DO AL ilosc znakow przekazanych w argumentach 
		cmp AL, 1 					;	Sprawdzam czy ze spacja jest <= 1 znak - jesli tak to nie ma argumentow
		jbe ex						;	Brak argumentow
		; else 
		dec AL 						;	Pomijanie spacji ES:[81h] -> 1B 
		mov ArgStrLen, AL 			;	Do zmiennej dlugosc argumentow	 

		xor CX, CX
		mov CL, AL					;	Ustawienie licznika petli
		
		mov SI, 82h					;	Poczatek ciagu argumentow - pomijam spacje ES:[81h] -> 1B 
		mov DI, offset ArgTab		;	DI bedzie adresowac przesuniecia offsetu tavlicy
		xor AX, AX 					;	Przyjmuje nastepujaca konwencje AL -> aktualny znak
									;	AH -> ilosc znakow argumentu (zaakceptowanych)
		mov BX, offset ArgOffsets	
		reading:					;	Petla wczytujaca kolejne znaki
			mov AL, ES:[SI]
			call HandleCharacter
			inc SI
		loop reading
		
		mov [DI], byte ptr "$"		; 	Upewnienie sie co do znaku dolara na koncu
		inc AH 						; 	Zwiekszenie dlugosci
		mov [BX], AH 				;	Przypisanie dlugosci do zakanczanego argumentu

		ex:							; 	Trzeba zdjac ze stosu to co sie nalozylo, zeby nie bylo problemu z powrotem
		popa

		ret

	ParseArguments endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury ParseArguments
	;-------------------------------------------------------------------------------------------------------------

	
	;-------------------------------------------------------------------------------------------------------------
	;
	;	Procedura Terminate
	;	Konczy program
	; 	IN: 	REGISTERS:	none
	;			MEMORY:		errorMsgOff, corrupChar, ArgTab, pos
	;	OUT: 	none
	;	DESC:	W zmiennej errorMsgOff znajduje się (po uruchomieniu funkcji Validate) offset do lancucha znakow,
	;			ktory przechowuje tresc wiadomosci zwrotnej do uzytkownika. Na początku jest ona wypisywana.
	;			Jeżeli okaże się, że zmienna corrupChar nie zmienila swojej wartosci poczatkowej (33d) - Procedura
	;			nie robi nic innego. W przeciwnym razie Nastepuje sprawdzenie, czy numer zepsutego znaku jest 
	;			liczba jedno- czy dwucyfrowa - wszystko w celu sarsowania numeru znaku na tekst i przekazania do
	;			tablicy corCharTxt (stad przesuniecie o 30h - aby uzyskac kod ASCII cyfry). Wypisywany jest numer
	;			znaku ktory nie nalezy do zakresu [0-9a-f] a nastepnie po przejsciu do nowej linii - wypisywany 
	;			jest 1. argument. W kolejnel linii jest wypisywany znak ^ pod znakiem, ktory jest wadliwy. W tym
	;			celu bufor pos wypelniam spacjami corrupChar - 1 razy, a na odpowiedniej pozycji wstawiam ^.
	;
	;-------------------------------------------------------------------------------------------------------------


	Terminate proc
		
		mov AX, seg errorMsgOff
		mov DS, AX
		mov DX, errorMsgOff
		mov AH, 9
		int 21h
		cmp corrupChar, 33d
		je go
			cmp corrupChar, 10			;	Sprawdzam czy liczba jedno- czy dwu- cyfrowa
			jb single
				xor AX, AX
				mov AL, corrupChar  	;	Dzielenie przez 10d - dzielna w AX, div w AL, mod w AH
				div d
				add AL, byte ptr 30h
				add AH, byte ptr 30h
				mov corCharTxt, AL
				mov corCharTxt[1], AH
				jmp prt
			single:
				mov AL, corrupChar		;	Dodaje 30h aby uzyskac kod ASCII
				add AL, byte ptr 30h
				mov corCharTxt, AL
			prt:
				mov AX, seg corCharTxt
				mov DS, AX
				mov DX, offset corCharTxt
				mov AH, 9
				int 21h

				mov AX, seg endl 		; 	Przejscie do nowej linii
				mov DX, AX
				mov DX, offset endl
				mov AH, 9
				int 21h

				mov AX, seg ArgTab 		;	Wypisanie 1. argumentu na ekran
				mov DS, AX
				MOV AL, 2h
				call GetArg
				mov DX, AX
				mov AH, 9
				int 21h

				mov DX, offset endl 		; 	Przejscie do nowej linii
				mov AH, 9
				int 21h

				;mov AX, seg pos
				;mov DS, AX
				mov SI, offset pos 			;	Bufor pos - nalezy wypelnic spacjami i znakiem ^
				xor AX, AX
				mov AL, corrupChar	
				dec AL 						;	Teraz AL ma ilosc spacji do wpisania
				xor CX, CX
				mov CL, AL
				lp: 						;	W petli wpisywane sa spacje
					mov [SI], byte ptr 20h
					inc SI
					loop lp 
				mov [SI], byte ptr 5Eh 		;	Na pozycji w buforze o numerze corrupChar - znak ^

				;mov AX, seg pos
				;mov DS, AX
				mov DX, offset pos 			;	Wypisanie
				mov AH, 9
				int 21h
		go:
			mov AH, 4CH
			int 21h
		
	Terminate endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury Terminate
	;-------------------------------------------------------------------------------------------------------------


	;-------------------------------------------------------------------------------------------------------------
	;
	;	Procedura HandleCharacter(PRIVATE)
	;	Konczy program
	; 	BIDIRECT: 	AL -> znak, AH -> ilosc znakow argumentu (ktore juz posiada)
	;				DI -> offset do zapisania kolejnego znaku
	;				SI -> Czytany offset
	;				BX -> przesuniecie wzgledem tablicy ArgOffsets
	;	OUT: 		modyfikacja podanych wyzej rejestow
	;	DESC:		Procedura sprawdza najpierw czy AL (znak) ma kod ASCII znaku CR, lub LF. Wowczas przechodzi 
	;				do etykiety CRLEEncounter.
	;				CRLEEncounter:
	;					Jesli ilosc znakow w przetwarzanym argumencie jest rozna niz zero - nalezy zakonczyc 
	;					ten argument - skok do CloseArgument
	;					W przwciwnym razie skok do HandleCharacterFinalizer - wyjscie z procedury
	;				Jezeli nie bylo skoku to sprawdzane jest czy znak to inny znak niedrukowalny 
	;				(kod ASCII <= 20h). Jezei tak to skok do OtherWhiteCharEncounter
	;				OtherWhiteCharEncounter:
	;					Jesli ilosc znakow w przetwarzanym argumencie jest rozna niz zero - wystepuje bialy znak
	;					po argumencie i trzeba skoczyc do CloseArgument, w przeciwnym razie wychodzimy - nic nie
	;					robiac (w glownej petli oczywiscie zmienia sie SI - ktore wskazuje na znak do badania)
	;				Jeżeli to jednak nie byl bialy znak sprawdzane jest czy jest to pierwszy czy kolejny znak
	;				argumentu. Pierwszy -> skok do OpenNewArg
	;				OpenNewArg:
	;					Zwiekszenie liczby argumentow i skok do AddCharToArg
	;				AddCharToArg:
	;					Obsluga dodawania znaku do listy argumentow. Do DS:[DI] - kolejny bajt w tablicy ArgTab
	;					dopisywany jest dany znak. DI jest przestawiany na kolejny bajt, zwiekszana jest liczba
	;					znakow argumentu. Potem nastepuje wyjscie.
	;				CloseArgument:
	;					Zwiekszenie AH ($ na koncu tez zajmuje miejsce) i wpisanie liczby do DS:[BX] - czyli 
	;					kolejnej komorki ArgOffsets. BX jest przestawiany o bajt do przpodu, AH jest zerowane,
	;					do DS:[DI] wpisany jest znak terminujacy argument ($), przestawiany jest [DI] na kolejny
	;					bajt i wychodzimy.
	;				HandleCharacterFinalizer:
	;					Powrot do caller'a.   
	;
	;-------------------------------------------------------------------------------------------------------------


	HandleCharacter proc
		
		; Nie modyfikuje rejestrow nieswiadmie - nie odkladam nic na stos

		
		cmp AL, 0Dh
		je CRLEEncounter 						; Napotkano CR
		cmp AL, 0Ah
		je CRLEEncounter						; Napotkano LF
		cmp AL, 20h
		jbe OtherWhiteCharEncounter 			;	AL <= 20h - napotkano bialy znak (inny niz CR LF)
		;	czyli jeednak napotkano znak drukowany
		
		cmp AH, 0d 								;	Znaleziono znak otwierajacy nowy argument
		je OpenNewArg
		jmp AddCharToArg						; 	else - Dodanie znaku do istniejaceg argumentu

		CRLEEncounter:
			cmp AH, 0d
			jne CloseArgument					;	AH != 0 -> bialy znak PO argumencie
			jmp HandleCharacterFinalizer
		
		OtherWhiteCharEncounter:
			cmp AH, 0d
			jne CloseArgument					;	AH != 0 -> bialy znak PO argumencie
			jmp HandleCharacterFinalizer

		OpenNewArg:
			inc ArgNumber
			jmp AddCharToArg

		AddCharToArg:
			mov [DI], AL
			inc DI
			inc AH
			jmp HandleCharacterFinalizer

		CloseArgument:
			inc AH

			mov [BX], AH 						;	Przypisanie dlugosci do zakanczanego argumentu
			inc BX
			xor AH, AH 							; 	Zerowanie ilosci znakow argumentu
			mov [DI], byte ptr "$"				;	Wpisanie $ na koncu argumentu
			inc DI	
			jmp HandleCharacterFinalizer

		HandleCharacterFinalizer:
			ret
		
	HandleCharacter endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury HandleCharacter
	;-------------------------------------------------------------------------------------------------------------


	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura PrintArguments
	;	Wypisuje argumenty
	; 	IN: 	REGISTERS: 	none
	;			MEMORY:		ArgNumber, ArgTab, ArgOffsets, endl
	;	OUT: 	none
	;	DESC:	Procedura dokoknuje wypisania na ekran argumentow podanych do parsera
	;			Najpierw ustawiony jes licznik (CL) na ilosc argumentow
	;			Tablica ArgTab: arg1$arg2$arg3$...argN$
	;			Tablica ArgOffsets: (:0d)LenA1(:1d)LenA2...(:Nd)LenAN
	;			DX jest ustawiony na offset ArgTab - początek tablicy argumentow - po zlozeniu DS:DX - mamy adres 
	;			fizyczny poczatku argumentu (DX bedzie sie zmieniac). BX wskazuje na przesuniecie (offset) tablicy 
	;			ArgOffsets (baza nadal to DS, wiec DS:BX da nam kolejne komorki pamieci - kolejne dlugosci
	;			kolejnych argumentow.) W petli ConsoleWrite najpierw wypisuje na ekran z adresu DS:DX, nastepnie 
	;			dodaje dlugosc tego argumentu do DX, wiec kolejny wypis. ciag znakow zaczyna sie od DS:(DX + [BX]), 
	;			gdzie [BX] wskazuje na dlugosc poprzedniego argumentu, dopiero potem przechodzimy do kolejnego 
	;			pola BX. Zabezpieczam DX i wypisuje zmienna endl - przejscie do nowej linii
	;			
	;-------------------------------------------------------------------------------------------------------------


	PrintArguments proc
		
		pusha						;	Odlozenie na stos rejestrow

		XOR CX, CX					;	Wyzerowanie CX
		mov CL, ArgNumber			;	Ustawienie licznika na ilosc argumentow
		cmp CL, 0d
		je fin

		mov DX, offset ArgTab		;	pobranie offsetow ArgTab i ArgOffsets do DX i BX
		mov BX, offset ArgOffsets
		ConsoleWrite:
			mov AX, seg ArgTab		;	poprawienie wartosci DS
			mov DS, AX
			mov AH, 9		
			int 21h					;	Wypisanie na ekran kolejnego argumentu

			;add DL, [BX]			;	Przesuniecie na kolejny argument
			;inc BX	
			xor AX, AX
			mov AL, [BX]
			add DX, AX				;	Przesuniecie na kolejny argument
			inc BX					; 	Pod [BX] - dlugosc kolejnego argumentu

			push DX					;	Zabezpieczam DX

			mov AX, seg endl		
			mov DS, AX
			mov DX, offset endl 	;	Wypisanie przejscia do nowej linii
			mov AH, 9
			int 21h
			
			pop DX					;	DX z powrotem ze stosu
			loop ConsoleWrite
		fin:
			popa 						;	Przywrocenie wartosci rejestrow ze stosu
			ret
		
	PrintArguments endp

	;----------------------------------------------------------------------------------------
	;	Koniec procedury PrintArguments
	;----------------------------------------------------------------------------------------



	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura GetArg
	;	Wypisuje argumenty
	; 	IN: 	REGISTERS: 	AL -> numer argumentu do pobrania
	;			MEMORY:		ArgNumber, ArgTab, ArgOffsets
	;	OUT: 	AX -> offset argumentu
	;	DESC:	Procedura zwraca w AX offset odpowiedniego argumentu. Najpierw zabezpieczana jest wartosc 
	;			rejestrow, nastepnie sprawdzamy, czy nie odwolujemy sie do argumentu poza zakresem - jesli tak
	;			-> wywolanie obslugi bledu. nastepnie CL jako licznik jest ustawiany na o jeden mniej niz numer
	;			argumentu. Do bazwoego offsetu dodajemy dlugosci wszystkich poprzedzajacych go argumentow w petli 
	;			while (etykieta testif)
	;			
	;-------------------------------------------------------------------------------------------------------------


	GetArg proc
		
		push CX						;	Odlozenie na stos rejestrow ktore beda wykorzystane
		push BX
		push DX

		XOR CX, CX					;	Wyzerowanie CX

		cmp AL, ArgNumber			; 	Jesli proba odwolania sie do nieistniej. argumentu - wyjatek
		ja ErrHandling 				;	AL > ArgNumber
		; else
		dec AL
		mov CL, AL 					;	Ustawienie licznika na ilosc argumentow

		mov AX, offset ArgTab		;	pobranie offsetu ArgTab do AX
		mov BX, offset ArgOffsets 	;	pobranie offsety ArgOffsets do BX
		
		testif:						; while (CL > 0)
			cmp CL, 0d
			je afterLoop 
			xor DX, DX
			mov DL, [BX]
			add AX, DX				;	Zwiekszenie offsetu o dlugosc poprzedniego argumentu
			inc BX					; 	Pod [BX] - dlugosc kolejnego argumentu
			dec CL
			jmp testif

		afterLoop:
		pop DX 						;	Przywrocenie wartosci rejestrow ze stosu
		pop BX
		pop CX 						
		
		ret
		
		;	Obsluga bledu
		ErrHandling:
			pop DX 						;	Przywrocenie wartosci rejestrow ze stosu
			pop BX
			pop CX 	
			push AX
			mov AX, offset nonExiArgEx
			mov errorMsgOff, AX
			pop AX
			call Terminate		

	GetArg endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury GetArg
	;-------------------------------------------------------------------------------------------------------------




	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura ValidateArgs
	;	Wypisuje argumenty
	; 	IN: 	REGISTERS: 	none
	;			MEMORY:		ArgNumber, ArgTab, ArgOffsets, reqNumArg
	;	OUT: 	none
	;	DESC:	Procedura kolejno waliduje argumenty i wywoluje procedury obslugi bledow. Najpierw sprawdzana jest
	;			ilosc podanych argumentow. Jesli mniejsza -> ToFewArgsException; jesli wieksza -> ToManyArgsException
	;			ToManyArgsException:
	;				Nie jest ta blad krytyczny. Do zmiennej errorMsgOff wpisywany jest offset odpowiedniego 
	;				komunikatu. Nastepnie skok do etykiety backToTrack
	;			ToFewArgsException:
	;				Blad krytyczny: do errorMsgOff - odpowieni offset komunikatu, zdjecie zapisanych na stosie
	;				rejestrow i zakonczenie programu - wezwanie proceury Terminate
	;			Kolejne sprawdzenie - tryb wypisywania:
	;			mode:
	;				Przez procedure GetArg pobierany jest drugi argument. Sprawdzenie czy kod ASCII tego argumentu
	;				to znak 0 lub 1, a takze czy dlugosc argumentu jest rowna 2 (wszak bedzie to 0$ lub 1$ -> OK)
	;				Jesli cos jest nie tak -> ModeException
	;			ModeException:
	;				Podobnie jak kazda etykieta z bloku Exceptions. Odpowiedni offset stringu bledy laduje w 
	;				errorMsgOff i wywolanie Terminate
	;			Nastepnie sprawdzamy dlugosc klucza SSH
	;			SSHKeyLength:
	;				Sprawdznie czy dlugosc klucza SSH (1. argument) to 33d (znak $ na koncu), jelsi nie ->
	;				InvalidSSHKeyLengthException
	;			InvalidSSHKeyLengthException:
	;				Podobnie jak kazda etykieta z bloku Exceptions. Odpowiedni offset stringu bledy laduje w 
	;				errorMsgOff i wywolanie Terminate
	;			Na koniec walidacja zestawu znakow [0-9a-f] w 1. argumencie:
	;			SSHValidation:
	;				W petli while sprawdzane sa kolejne kody ASCII znakow 1. argumentu. Jesli sa mniejsze niz
	;				znak "0" albo wieksze niz "f" -> InvalidHEXNumException
	;				Potem sprawdzenie czy kod znaku jest mniejszy niz ":", ktory nastepuje po "9" w kodzie
	;				ASCII albo czy wiekszy niz "`", ktory poprzedza "a". Jesli alternatywa nie spelniona ->
	;				InvalidHEXNumException. W przeciwnym razie zwiekszenie SI - offsetu wskazujacego na kolejne
	;				znaki oraz CL - licznika petli. Po petli whiile skok do pExit - zdjecie ze stosu i powrot
	;			InvalidHEXNumException:
	;				Podobnie jak kazda etykieta z bloku Exceptions. Odpowiedni offset stringu bledy laduje w 
	;				errorMsgOff i wywolanie Terminate. Przed wyjsciem zapisuje jeszcze w zmiennej corrupChar numer
	;				znaku, na ktorym wystapil blad.				
	;			
	;-------------------------------------------------------------------------------------------------------------


	ValidateArgs proc
		
		pusha

		numberOfArgs:
			mov AL, ArgNumber 				;	unikam porownywania dwoch wartosci z pamieci
			cmp AL, reqNumArg
			jb ToFewArgsException 			; 	AL < reqNumArg 
			ja ToManyArgsException			; 	AL > reqNumArg
		backToTrack:						;	Jesli jest za duzo argumentow program da tylko warning, ale 
											; 	bedzie dzialal dalej

		mode:
			mov AL, 1h
			call GetArg
			mov SI, AX
			cmp DS:[SI], byte ptr 30h		;	Sprawdzam, czy kod ASCII znaku nalezy do [30h, 31h]
			jb ModeException
			cmp DS:[SI], byte ptr 31h
			ja ModeException
			mov SI, offset ArgOffsets		;	Sprawdzam czy dlugosc argumentu wynosi 1 (2 ze znakiem $)
			cmp [SI], byte ptr 2d
			jne ModeException


		SSHKeyLength:
			mov SI, offset ArgOffsets
			inc SI 								;	Sprawdzam czy dlugosc argumentu 2 wynosi 16 (17 ze znakiem $)
			cmp [SI], byte ptr 33d
			jne InvalidSSHKeyLengthException

		SSHValidation:							;	SPrawdzam czy klucz SSH sklada sie z odpowiednich znakow
			xor CX, CX
			mov AL, 2h
			call GetArg							;	Pobranie drugiego argumentu (linia nizej)
			mov SI, AX 							;	Tutaj mozna juz bezpiecznie zalozyc ze tablica nie jest pusta
			whileLoop:						; while (CL < 32d)
			cmp CL, 32d
				je afterWhileLoop 

				cmp DS:[SI], byte ptr 30h		;	kod ASII znaku < 30h - znak "0"
				jb InvalidHEXNumException
				cmp DS:[SI], byte ptr 66h		;	kod ASII znaku > 66h - znak "f"
				ja InvalidHEXNumException

				cmp DS:[SI], byte ptr 3Ah		;	kod ASCII znaku < 3Ah - co najwyzej znak "9" jb -> a<b
				jb next1						;	jezeeli kod > 34h - sprawdz czy tez wiekszy od 60h - naczej blad
					cmp DS:[SI], byte ptr 60h	;	kod ASCII znaku > 60h - co najwyzej znak "a"
					ja next1
					jmp InvalidHEXNumException
				next1:
					inc SI						; 	Pod [SI] - kolejny znak
					inc CL
					jmp whileLoop
			afterWhileLoop:

		jmp pExit
		;------------------------
		;|		Exceptions:		|
		;------------------------	

		ToFewArgsException:	
			mov AX, offset toFewArgEx
			mov errorMsgOff, AX
			popa
			jmp Terminate

		ToManyArgsException:
			mov AX, offset toManyArgEx
			mov errorMsgOff, AX
			jmp backToTrack

		ModeException:
			mov AX, offset secArgEx
			mov errorMsgOff, AX
			popa
			call Terminate

		InvalidSSHKeyLengthException:
			mov AX, offset InvSSHLenEx
			mov errorMsgOff, AX
			popa
			call Terminate

		InvalidHEXNumException:
			mov AX, offset corCharEx
			mov errorMsgOff, AX
			inc CL
			mov corrupChar, CL 				;	Pokaze, ktory znak jako pierwszy jest bledny
			popa
			call Terminate

		pExit:								; 	Trzeba zdjac ze stosu to co sie nalozylo, zeby nie bylo problemu z powrotem
			popa
			ret

	ValidateArgs endp

	;------------------------------------------------------------------------------------------------------------
	;	Koniec procedury ValidateArgs
	;------------------------------------------------------------------------------------------------------------




	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura GetByteFromSSHKey
	;	Zwraca wartosc wskazanego bajtu
	; 	IN: 	REGISTERS: 	AL -> numer bajtu - numeracja od 0!
	;			MEMORY:		ArgTab
	;	OUT: 	AL -> wartosc bajtu
	;	DESC:	Zwraca do funkcji wywolujacej przez AL wartosc bajtu z klucza SSH. Najpierw zabezpieczane sa 
	;			rejestry. Potem pobierane jest odpowiednie przesuniecie wzgledem 1. argumentu. Kiedy juz DS:[SI]
	;			wskazuje poczatek bajtu - pierwsza cyfra HEX jest pobrana do AL, a wowczas wywolywana jest Procedura
	;			GetValueOfHex, ktora zwroci liczbowa wartosc liczby HEX - z tym ze narazie jest to znak
	;			w kodzie ASCII. Umieszczana jest ona w AH, bo chcemy miec liczbe < 255 w AX - a caly rejestr jest
	;			uzywany w operacji mul. Zeruje wiec AL, a caly AX wyglada tak: 0000|xxxx. Wykonywane jest mnozenie
	;			Wiadomo ze 15x16 da 240, czyli znowu po wykonaniu mnozenia AX: 0000|xxxx. Dla ulatwienia cala
	;			wartosc przenosimy do DL. Zwiekszamy wskaznik SI, zerujemy AX - i przez wywolanie procedury 
	;			GetValueOfHex w AL (starszym bajcie liczby z AX) mamy wartosc kolejnej czworki bitow. dodajemy
	;			DL do AL i w AL mamy wartosc ostateczna bajtu. Uwaga: Wiadomo ze nie nastapi przepelnienie AL 
	;			i napisanie AH, gdyz maksymalna wartosc bajtu to 255, czyli 11111111(2)
	;			
	;-------------------------------------------------------------------------------------------------------------


	GetByteFromSSHKey proc
		
			push CX
			push DX
			push SI
			
			xor CX, CX
			mov CL, AL
			push AX
			mov AL, 2h
			call GetArg
			mov SI, AX
			pop AX

			shl CL, 1d 			; 	Szybkie mnozenie x 2

			lp:					;	Pobranie offsetu poczatku bajtu do przeliczenia
			cmp CL, 0d
			je koniec
			inc SI
			dec CL	
			jmp lp		
			koniec:

			xor AX, AX 			;	mnozenie przez 1B bedzie dzialalo na AL a zwroci wynik do AX
			mov AL, DS:[SI]
			call GetValueOfHex
			mul hex 			;	Zmienna zawiera podstawe systemu szesnastkowego
			mov DL, AL			;	Zabezpieczeniw wyniku -> operacja da max 240 (1B) bedzie to mlodszy Bajt AX, czyli AL
			inc SI
			xor AX, AX
			mov AL, DS:[SI]
			call GetValueOfHex
			add AL, DL

			pop SI
			pop DX
			pop CX
			ret

	GetByteFromSSHKey endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury GetByteFromSSHKey
	;-------------------------------------------------------------------------------------------------------------



	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura GetValueOfHex
	;	Zwraca wartosc wskazanego bajtu
	; 	IN: 	REGISTERS: 	AL -> kod ASCII znaku (poprawnej liczby HEX!!!)
	;	OUT: 	AL -> wartosc 4 bitow	
	;			
	;-------------------------------------------------------------------------------------------------------------


	GetValueOfHex proc
		
		cmp AL, byte ptr 39h		;	Jesli 0-9
		ja AFHandle 				;	Jesli AL > 39h
			sub AL, byte ptr 30h
			jmp finPrc				;	Przeskoczenie na koniec
		AFHandle:
			sub AL, 87d				;	kod ASCII a: 97d -> 97-87 = 10d = 0Ah
		finPrc:
			ret

	GetValueOfHex endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury GetValueOfHex
	;-------------------------------------------------------------------------------------------------------------


	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura AnalizeSSHKey 
	;	Analizuje klucz SSH pod katem ruchow skoczka
	; 	IN: 	REGISTERS: 	none
	;			MEMORY:		ArgTab, binMask
	;	OUT: 	none	
	;	DESC:	Procedura dokonuje analizy kolejnych dwubitow - od najmlodszego kolejnych (od najstarszego)
	;			bajtow klucza SSH. W petli while sprawdzamy czy licznik - tutaj AL nie przekroczyl 16d. Odlozenie
	;			licznika na stos i pobranie odpowiedniego bajtu (wyznaczanego przez AL -licznik) do AX.
	;			Zaladowanie do binMask maski binarnej ktora w operacji AND bedzie odkrywac tylko i wylacznie
	;			dwa sasiednie bity. Licznik CL usawiony na 4 - sa 4 x 2b w 1B i wyzerowanie BL. Zachowanie znowu
	;			AX na stosie (wartosc binarna bajtu), operacja AND na AL i binMask - odkryje nam tylko jeden dwubit
	;			Odlozenie na stos licznika i zaladowanie do niego BL (shr wymaga CL lub danej natychmiastowej)
	;			BL - przesuniecie jedynek w masce od prawej - nalezy wiec AL (po operacji AND) dosunac do prawej offset
	;			odpowiednia ilosc bitow. Zebrana ze stosu jest wartosc CX i wywolana procedura MoveFigure
	;			Nastepnie maska jest przesowana cyklicznie o 2 miejsca w lewo, do BL dodawane jest 2 i tak do konca 
	;			Bajtu. Po wyjsciu z lp zdejmujemy AX - bedzie to nasz glowny licznik i zwiekszamy o 1.
	;			Na koncu wypisujemy przejscie do nowej linii.
	;			
	;-------------------------------------------------------------------------------------------------------------


	AnalizeSSHKey proc
		
		pusha
			mov AL, 2h
			call GetArg
			mov SI, AX
			XOR AX, AX

			whileLoop:
				cmp AL, 16d
				je finish
					push AX
					call GetByteFromSSHKey
	; Weźmy maske i robmy przesuniecia bitowe ROL 00000011 -> 00000110 -> 00001100 -> OPERACJA AND z wartoscia bajtu
					mov binMask, 00000011b
					xor CX, CX
					mov CL, 4d
					xor BL, BL
					lp:
						push AX
						and AL, binMask
						;; Tutaj umescic obsluge odczytywania ruchu! - W AL jest teraz interesujacy nas dwubit - trzeba go dosunac do prawej
						push CX
						mov CL, BL
						shr AL, CL 			; 	Dosuniecie do prawej - od 0, 2, 4, 6 pozycji moze byc tylko CL
						pop CX
						call MoveFigure

						rol binMask, 2d
						add BL, 2d
						pop AX
						loop lp
					pop AX
					inc AL
				jmp whileLoop

		finish:
		mov AH, 9
		mov DX, offset endl
		int 21h
		popa
		ret

	AnalizeSSHKey endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury AnalizeSSHKey
	;-------------------------------------------------------------------------------------------------------------


	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura MoveFigure 
	;	Przemieszcza figure
	; 	IN: 	REGISTERS: 	AL - wartosc dwoch bitow 
	;			MEMORY:		actFigPos, ASCIIArtTab
	;	OUT: 	none	
	;	DESC:	Pobieramy drugi argument (tryb przechadzki gonca).
	;			W trybie normalnym do BL wpisujemy wartosc bajtu AL - bedzie ona oznaczac kierunek ruchu.
	;			Do AL wczytuje actFigPos oznaczajaca aktualna pozycje gonca. Na poczatek jest to srodek szachownicy
	;			w moim programie pole: 93d. Dzielimy pozycje gonca przez divider (21d - pierwsze pole wiersza to |,
	;			a trzy ostatnie to "|", 10h, 13h). Nastepnie sprawdzamy w ktora strone goniec mialby sie ruszyc
	;			i nastepuje skok do odpowiednich etykiet oznaczajcych kierunek. Tam sprawdzane jest czy mozliwe
	;			jest dane przesuniecie - w tym detekcja rogu i odpowiednie operacje na zmiennej actFigPos sa 
	;			wykonywane. Analogicznie w trybie wiezy. Po zakonczeniu ruchu w etykiecie continue. Do SI 
	;			laduje offset ASCIIArtTab, ktora teraz jeszcze przechowuje ilosc odwiedzin danego pola. Do AL
	;			leci aktualna pozycja, zwiekszam o nia offset SI i do tego pola dodaje 1d.
	;
	;-------------------------------------------------------------------------------------------------------------


	MoveFigure proc
		
		pusha
		push AX
		mov AL, 1h
		call GetArg					;	W AX mamy offset drugiego argumentu
		mov SI, AX
		cmp DS:[SI], byte ptr 31h
		pop AX
		je special
			mov BL, AL
			mov AL, actFigPos
			div divider
			cmp BL, 0d 	;	AL = 00000000
			je zz
			cmp BL, 1d 	;	AL = 00000001
			je zo
			cmp BL, 2d 	;	AL = 00000010
			je oz
			cmp BL, 3d 	;	AL = 00000011
			je oo

			zz:	
				cmp AL, 0d
				je ZZsecond
				sub actFigPos, 21d		; mozliwe przesuniecie w gore
				ZZsecond:
				cmp AH, 1d
				je continue
				dec actFigPos					; mozliwe przesuniecie w lewo
				jmp continue
			zo:	
				cmp AL, 0d
				je ZOsecond
				sub actFigPos, 21d		; mozliwe przesuniecie w gore
				ZOsecond:
				cmp AH, 17d
				je continue
				inc actFigPos					; mozliwe przesuniecie w prawo
				jmp continue
			oz:	
				cmp AL, 8d
				je OZsecond
				add actFigPos, 21d		; mozliwe przesuniecie w dol
				OZsecond:
				cmp AH, 1d
				je continue
				dec actFigPos					; mozliwe przesuniecie w lewo
				jmp continue
			oo:				
				cmp AL, 8d
				je OOsecond
				add actFigPos, 21d		; mozliwe przesuniecie w dol
				OOsecond:
				cmp AH, 17d
				je continue
				inc actFigPos					; mozliwe przesuniecie w prawo
				jmp continue
				
		special:				;	TRYB WIEZY
			mov BL, AL
			mov AL, actFigPos
			div divider
			cmp BL, 0d 	;	AL = 00000000
			je szz
			cmp BL, 1d 	;	AL = 00000001
			je szo
			cmp BL, 2d 	;	AL = 00000010
			je soz
			cmp BL, 3d 	;	AL = 00000011
			je soo

			szz:
				cmp AL, 0d
				je continue					
				sub actFigPos, 21d		;	Mozliwe przesuniecie do gory
				jmp continue
			szo:
				cmp AH, 17d
				je continue
				inc actFigPos					;	Mozliwe przesuniecie w prawo
				jmp continue
			soz:
				cmp AH, 1d
				je continue
				dec actFigPos					;	Mozliwe przesuniecie w lewo
				jmp continue
			soo:
				cmp AL, 8d
				je continue					
				add actFigPos, 21d		;	Mozliwe przesuniecie w dol
		continue:
		mov SI, offset ASCIIArtTab
		xor AX, AX
		mov AL, actFigPos
		add SI, AX
		xor AX, AX
		mov AL, 1d
		add DS:[SI], AL				; 	Zwiększenie licznika odwiedzin
		popa
		ret

	MoveFigure endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury MoveFigure
	;-------------------------------------------------------------------------------------------------------------




	;-------------------------------------------------------------------------------------------------------------
	;	
	;	Procedura PrintChart 
	;	Wyswietla ASCII Art
	; 	IN: 	REGISTERS: 	none 
	;			MEMORY:		actFigPos, ASCIIArtTab, translate
	;	OUT: 	none	
	;	DESC:	Procedura wypisywania ASCII Art. Bufor translate posiada w odpowiednich offsetach (ilosc odwiedzin)
	;			odpowiednie znaki do wypisania. Analizowane sa kolejne pola az do BBh (21 * 9 - 2 (ostatnie 10h, 13h))
	;			Petla przechodzi po kazdym z pol i sprawdza czy nie jest to pole nie do zmiany (poczatowe i 3 ostanie
	;			w wierszu) Nastepnie sprawdzane jest ile w danym polu bylo odwiedzin i ladowane to jest do BL.
	;			Jesli odwiedzin > 14 - i tak znak "^", jesli nie do DI (offsetu translate) dodajemy ilosc odwiedzin
	;			BX (wlasciwie BL) i do [BH] ladujemy odpowiedni znak. Nastepnie pod odpowiedni offset tablicy
	;			ASCIIArtTab wrzucamy ten znak. Na koniec w poczatkowym polu [SI + 93d] jest umieszczany znak "S", a na 
	;			polu koncowym [SI + actFigPos] - znak "E". Dla przejrzystosci ASCII Art otacza ramka.
	;			
	;-------------------------------------------------------------------------------------------------------------


	PrintChart proc
		
		pusha
		xor CX, CX
		mov SI, offset ASCIIArtTab 		;	Ustawiamy SI na poczatek tablicy z odwiedzinami
		mov DI, offset translate
		whileLoop:
		cmp CL, 0BBh
		je afterLoop
			xor AX, AX
			mov AL, CL
			div divider
			cmp AH, 18d		;	Przechodzimy przez jedno z dwoch pol koncowych wiersza - znaki: 10, 13 - nie ruszamy!
			jae increment
			cmp AH, 0d
			je increment 	;	Pole z | na pocztku

			xor BX, BX
			mov BL, [SI]
			cmp [SI], byte ptr 14d
			jae	moreEqual14
			mov BH, [DI + BX]
			mov [SI], BH
			jmp increment
			moreEqual14:
				mov BH, [DI + 14d]
				mov [SI], BH

			increment:
				inc CL
				inc SI
				jmp whileLoop
		afterLoop:
			mov SI, offset ASCIIArtTab		;	Na koncu na polu poczatkowym i koncowym S, E
			add SI, 93d
			mov [SI], byte ptr 53h
			mov SI, offset ASCIIArtTab
			xor AX, AX
			mov AL, actFigPos
			add SI, AX
			mov [SI], byte ptr 45h
			
			mov AX, seg line
			mov DS, AX
			mov DX, offset line
			mov AH, 9
			int 21h

			mov AX, seg ASCIIArtTab
			mov DS, AX
			mov DX, offset ASCIIArtTab
			mov AH, 9
			int 21h

			mov AX, seg line
			mov DS, AX
			mov DX, offset line
			mov AH, 9
			int 21h

		popa
		ret

	PrintChart endp

	;-------------------------------------------------------------------------------------------------------------
	;	Koniec procedury PrintChart
	;-------------------------------------------------------------------------------------------------------------


code1 ends

;---------------------------------------------------------------------------------------------------------------------------------------
;|															SEGMENT KODU - KONIEC													   |
;---------------------------------------------------------------------------------------------------------------------------------------



;---------------------------------------------------------------------------------------------------------------------------------------
;|																SEGMENT STOSU														   |
;---------------------------------------------------------------------------------------------------------------------------------------

;	Deklaruje wielkosc stosu na 256 slow (512 B)
stack1 segment stack
		dw 	255 dup(?)
	top	dw 	?
stack1 ends

;---------------------------------------------------------------------------------------------------------------------------------------
;|															SEGMENT KODU - KONIEC													   |
;---------------------------------------------------------------------------------------------------------------------------------------

end start