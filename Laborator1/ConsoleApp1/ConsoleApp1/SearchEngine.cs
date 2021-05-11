using System;

using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Xml;
using System.Text.RegularExpressions;

namespace ConsoleApp1
{
    class SearchEngine
    {
        //**************************************************************************************************************************************************
        //Data declaration
        //***************************************************************************************************************************************************
        Dictionary<string, int> GlobalWords = new Dictionary<string, int>();
        Dictionary<string, int> FileTitleWords = new Dictionary<string, int>();
        Dictionary<string, int> FileTextWords = new Dictionary<string, int>();
        Dictionary<string, int> FileWords = new Dictionary<string, int>();
        string[] GlobalArray;
        string[] test;
        

        List<string> aux = new List<string>();
        string[] title_words, text_words;
        int Count_for_Files = 0;
        PorterStemmer stemmer = new PorterStemmer();
      
        int i, ct;

        //**************************************************************************************************************************************************
        //Function for Stemmming Words
        //***************************************************************************************************************************************************
        public class PorterStemmer
        {

            // The passed in word turned into a char array. 
            // Quicker to use to rebuilding strings each time a change is made.
            private char[] wordArray;

            // Current index to the end of the word in the character array. This will
            // change as the end of the string gets modified.
            private int endIndex;

            // Index of the (potential) end of the stem word in the char array.
            private int stemIndex;


            /// <summary>
            /// Stem the passed in word.
            /// </summary>
            /// <param name="word">Word to evaluate</param>
            /// <returns></returns>
            public string StemWord(string word)
            {

                // Do nothing for empty strings or short words.
                if (string.IsNullOrWhiteSpace(word) || word.Length <= 2) return word;

                wordArray = word.ToCharArray();

                stemIndex = 0;
                endIndex = word.Length - 1;
                Step1();
                Step2();
                Step3();
                Step4();
                Step5();
                Step6();

                var length = endIndex + 1;
                return new String(wordArray, 0, length);
            }


            // Step1() gets rid of plurals and -ed or -ing.
            /* Examples:
                   caresses  ->  caress
                   ponies    ->  poni
                   ties      ->  ti
                   caress    ->  caress
                   cats      ->  cat

                   feed      ->  feed
                   agreed    ->  agree
                   disabled  ->  disable

                   matting   ->  mat
                   mating    ->  mate
                   meeting   ->  meet
                   milling   ->  mill
                   messing   ->  mess

                   meetings  ->  meet  		*/
            private void Step1()
            {
                // If the word ends with s take that off
                if (wordArray[endIndex] == 's')
                {
                    if (EndsWith("sses"))
                    {
                        endIndex -= 2;
                    }
                    else if (EndsWith("ies"))
                    {
                        SetEnd("i");
                    }
                    else if (wordArray[endIndex - 1] != 's')
                    {
                        endIndex--;
                    }
                }
                if (EndsWith("eed"))
                {
                    if (MeasureConsontantSequence() > 0)
                        endIndex--;
                }
                else if ((EndsWith("ed") || EndsWith("ing")) && VowelInStem())
                {
                    endIndex = stemIndex;
                    if (EndsWith("at"))
                        SetEnd("ate");
                    else if (EndsWith("bl"))
                        SetEnd("ble");
                    else if (EndsWith("iz"))
                        SetEnd("ize");
                    else if (IsDoubleConsontant(endIndex))
                    {
                        endIndex--;
                        int ch = wordArray[endIndex];
                        if (ch == 'l' || ch == 's' || ch == 'z')
                            endIndex++;
                    }
                    else if (MeasureConsontantSequence() == 1 && IsCVC(endIndex)) SetEnd("e");
                }
            }

            // Step2() turns terminal y to i when there is another vowel in the stem.
            private void Step2()
            {
                if (EndsWith("y") && VowelInStem())
                    wordArray[endIndex] = 'i';
            }

            // Step3() maps double suffices to single ones. so -ization ( = -ize plus
            // -ation) maps to -ize etc. note that the string before the suffix must give m() > 0. 
            private void Step3()
            {
                if (endIndex == 0) return;

                /* For Bug 1 */
                switch (wordArray[endIndex - 1])
                {
                    case 'a':
                        if (EndsWith("ational")) { ReplaceEnd("ate"); break; }
                        if (EndsWith("tional")) { ReplaceEnd("tion"); }
                        break;
                    case 'c':
                        if (EndsWith("enci")) { ReplaceEnd("ence"); break; }
                        if (EndsWith("anci")) { ReplaceEnd("ance"); }
                        break;
                    case 'e':
                        if (EndsWith("izer")) { ReplaceEnd("ize"); }
                        break;
                    case 'l':
                        if (EndsWith("bli")) { ReplaceEnd("ble"); break; }
                        if (EndsWith("alli")) { ReplaceEnd("al"); break; }
                        if (EndsWith("entli")) { ReplaceEnd("ent"); break; }
                        if (EndsWith("eli")) { ReplaceEnd("e"); break; }
                        if (EndsWith("ousli")) { ReplaceEnd("ous"); }
                        break;
                    case 'o':
                        if (EndsWith("ization")) { ReplaceEnd("ize"); break; }
                        if (EndsWith("ation")) { ReplaceEnd("ate"); break; }
                        if (EndsWith("ator")) { ReplaceEnd("ate"); }
                        break;
                    case 's':
                        if (EndsWith("alism")) { ReplaceEnd("al"); break; }
                        if (EndsWith("iveness")) { ReplaceEnd("ive"); break; }
                        if (EndsWith("fulness")) { ReplaceEnd("ful"); break; }
                        if (EndsWith("ousness")) { ReplaceEnd("ous"); }
                        break;
                    case 't':
                        if (EndsWith("aliti")) { ReplaceEnd("al"); break; }
                        if (EndsWith("iviti")) { ReplaceEnd("ive"); break; }
                        if (EndsWith("biliti")) { ReplaceEnd("ble"); }
                        break;
                    case 'g':
                        if (EndsWith("logi"))
                        {
                            ReplaceEnd("log");
                        }
                        break;
                }
            }

            /* step4() deals with -ic-, -full, -ness etc. similar strategy to step3. */
            private void Step4()
            {
                switch (wordArray[endIndex])
                {
                    case 'e':
                        if (EndsWith("icate")) { ReplaceEnd("ic"); break; }
                        if (EndsWith("ative")) { ReplaceEnd(""); break; }
                        if (EndsWith("alize")) { ReplaceEnd("al"); }
                        break;
                    case 'i':
                        if (EndsWith("iciti")) { ReplaceEnd("ic"); }
                        break;
                    case 'l':
                        if (EndsWith("ical")) { ReplaceEnd("ic"); break; }
                        if (EndsWith("ful")) { ReplaceEnd(""); }
                        break;
                    case 's':
                        if (EndsWith("ness")) { ReplaceEnd(""); }
                        break;
                }
            }

            /* step5() takes off -ant, -ence etc., in context <c>vcvc<v>. */
            private void Step5()
            {
                if (endIndex == 0) return;

                switch (wordArray[endIndex - 1])
                {
                    case 'a':
                        if (EndsWith("al")) break; return;
                    case 'c':
                        if (EndsWith("ance")) break;
                        if (EndsWith("ence")) break; return;
                    case 'e':
                        if (EndsWith("er")) break; return;
                    case 'i':
                        if (EndsWith("ic")) break; return;
                    case 'l':
                        if (EndsWith("able")) break;
                        if (EndsWith("ible")) break; return;
                    case 'n':
                        if (EndsWith("ant")) break;
                        if (EndsWith("ement")) break;
                        if (EndsWith("ment")) break;
                        /* element etc. not stripped before the m */
                        if (EndsWith("ent")) break; return;
                    case 'o':
                        if (EndsWith("ion") && stemIndex >= 0 && (wordArray[stemIndex] == 's' || wordArray[stemIndex] == 't')) break;
                        /* j >= 0 fixes Bug 2 */
                        if (EndsWith("ou")) break; return;
                    /* takes care of -ous */
                    case 's':
                        if (EndsWith("ism")) break; return;
                    case 't':
                        if (EndsWith("ate")) break;
                        if (EndsWith("iti")) break; return;
                    case 'u':
                        if (EndsWith("ous")) break; return;
                    case 'v':
                        if (EndsWith("ive")) break; return;
                    case 'z':
                        if (EndsWith("ize")) break; return;
                    default:
                        return;
                }
                if (MeasureConsontantSequence() > 1)
                    endIndex = stemIndex;
            }

            /* step6() removes a final -e if m() > 1. */
            private void Step6()
            {
                stemIndex = endIndex;

                if (wordArray[endIndex] == 'e')
                {
                    var a = MeasureConsontantSequence();
                    if (a > 1 || a == 1 && !IsCVC(endIndex - 1))
                        endIndex--;
                }
                if (wordArray[endIndex] == 'l' && IsDoubleConsontant(endIndex) && MeasureConsontantSequence() > 1)
                    endIndex--;
            }

            // Returns true if the character at the specified index is a consonant.
            // With special handling for 'y'.
            private bool IsConsonant(int index)
            {
                var c = wordArray[index];
                if (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u') return false;
                return c != 'y' || (index == 0 || !IsConsonant(index - 1));
            }

            /* m() measures the number of consonant sequences between 0 and j. if c is
               a consonant sequence and v a vowel sequence, and <..> indicates arbitrary
               presence,

                  <c><v>       gives 0
                  <c>vc<v>     gives 1
                  <c>vcvc<v>   gives 2
                  <c>vcvcvc<v> gives 3
                  ....		*/
            private int MeasureConsontantSequence()
            {
                var n = 0;
                var index = 0;
                while (true)
                {
                    if (index > stemIndex) return n;
                    if (!IsConsonant(index)) break; index++;
                }
                index++;
                while (true)
                {
                    while (true)
                    {
                        if (index > stemIndex) return n;
                        if (IsConsonant(index)) break;
                        index++;
                    }
                    index++;
                    n++;
                    while (true)
                    {
                        if (index > stemIndex) return n;
                        if (!IsConsonant(index)) break;
                        index++;
                    }
                    index++;
                }
            }

            // Return true if there is a vowel in the current stem (0 ... stemIndex)
            private bool VowelInStem()
            {
                int i;
                for (i = 0; i <= stemIndex; i++)
                {
                    if (!IsConsonant(i)) return true;
                }
                return false;
            }

            // Returns true if the char at the specified index and the one preceeding it are the same consonants.
            private bool IsDoubleConsontant(int index)
            {
                if (index < 1) return false;
                return wordArray[index] == wordArray[index - 1] && IsConsonant(index);
            }

            /* cvc(i) is true <=> i-2,i-1,i has the form consonant - vowel - consonant
               and also if the second c is not w,x or y. this is used when trying to
               restore an e at the end of a short word. e.g.

                  cav(e), lov(e), hop(e), crim(e), but
                  snow, box, tray.		*/
            private bool IsCVC(int index)
            {
                if (index < 2 || !IsConsonant(index) || IsConsonant(index - 1) || !IsConsonant(index - 2)) return false;
                var c = wordArray[index];
                return c != 'w' && c != 'x' && c != 'y';
            }

            // Does the current word array end with the specified string.
            private bool EndsWith(string s)
            {
                var length = s.Length;
                var index = endIndex - length + 1;
                if (index < 0) return false;

                for (var i = 0; i < length; i++)
                {
                    if (wordArray[index + i] != s[i]) return false;
                }
                stemIndex = endIndex - length;
                return true;
            }

            // Set the end of the word to s.
            // Starting at the current stem pointer and readjusting the end pointer.
            private void SetEnd(string s)
            {
                var length = s.Length;
                var index = stemIndex + 1;
                for (var i = 0; i < length; i++)
                {
                    wordArray[index + i] = s[i];
                }
                // Set the end pointer to the new end of the word.
                endIndex = stemIndex + length;
            }

            // Conditionally replace the end of the word
            private void ReplaceEnd(string s)
            {
                if (MeasureConsontantSequence() > 0) SetEnd(s);
            }
        }
        //**************************************************************************************************************************************************
        //This function creates a global vector for words 
        //***************************************************************************************************************************************************

        string[]  CreateGlobalArray(Dictionary<string,int> GlobalDictionary)
        {
           string []GlobalArray = new string[GlobalDictionary.Count];
            int i = 0;
          foreach(var s in GlobalDictionary)
            {
                
                GlobalArray[i]= i + ":" + s.Value;//array shoul contain something like this 1:5 2:3 3:1
                i++;
            }
            return GlobalArray;
        }
        //**************************************************************************************************************************************************
        //This function is checking if words from Global Array are present in Local document ,and if they are i am setting their frequency    
        //***************************************************************************************************************************************************
        string[] CheckDocument(Dictionary<string,int> GlobalWords,int number_of_folder)
        {
            string[] documentStatus  = new string[GlobalArray.Length];
            string docPath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);
            Dictionary <string,int> temp = new Dictionary<string, int> ();//dictionary to get document content 
            
           
                string file_name = "OutputFileDocument" +(number_of_folder+1) + ".txt";
                StreamReader inputFile = new StreamReader(Path.Combine(docPath, file_name));

                string line;
                // Read and display lines from the file until the end of
                // the file is reached.
                int plm = 0;
                while ((line = inputFile.ReadLine()) != null)
                {
                    string[] character = line.Split(' ');
                    temp.Add(character[0], Int32.Parse(character[2]));
                }
                int ct=0;
            bool flag = false;
            foreach (KeyValuePair<string, int> kvp in GlobalWords)
            {

                foreach (KeyValuePair<string, int> word in temp)
                {


                    //checking if a word from global dictionary exists in local document
                    if (kvp.Key.Equals(word.Key))
                    {
                        documentStatus[ct] = ct + ":" + word.Value;
                        flag = true;
                    }
                   

                }
                if (flag != true)
                {
                    documentStatus[ct] = ct + ":" + 0;
                }
                ct++;
                flag = false;
            }
            return documentStatus;
        }
        //**************************************************************************************************************************************************
        //This function creates a vector for each document (vector has the same size as global vector and on each location contains if the word contained 
        //in global vector apears in  local vector (if yes put an 1:frequency if not put an 0:frequency)        
        //***************************************************************************************************************************************************
        string[] CreateLocalArray(string[] Array,int number_of_file)
        {
            string[] LocalVectors = new string[GlobalArray.Count()];//creez un array de dimensiunea vectorului global
            //first [] is for setting the number of lines ,how many vectors do i want to have
            //the second [] is for setting each vector size
            // Set a variable to the Documents path.
            string docPath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);


                string file_name = "OutputFileDocument" + (number_of_file  + 1) + ".txt";
                   LocalVectors = Array;
                


           
            return LocalVectors;
        }
        //**************************************************************************************************************************************************
        //This function implements stemming
        //***************************************************************************************************************************************************
        List<string> GetRidOfRoot(List<string> aux)
        {
            List<string> temp = new List<string>();

            for (int i = 0; i < aux.Count(); i++)
            {
                {
                    string stem = stemmer.StemWord(aux[i]);

                    
                        temp.Add(stem);
                    
                }
            }
            return temp;
        }


        //**************************************************************************************************************************************************
        //This function reads a file and extract title,text tag content spliting words by space 
        //***************************************************************************************************************************************************
        public void SingleFileReader()
        {

            //Citirea dintr-un fisier a tag-ului de title si text

            //citesc documentul si il incarc intr-un document nou
            string xmlFile = File.ReadAllText(@"E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_34\5697NEWS.xml");


            XmlDocument xmldoc = new XmlDocument();
            xmldoc.LoadXml(xmlFile);

            //Preiau continutul tag-ului de title
            XmlNodeList xnList = xmldoc.GetElementsByTagName("title");
            Console.WriteLine("Continutul tag-ului de title este :");
            Console.WriteLine();
            Console.WriteLine(xnList[0].InnerText.ToString());
            Console.WriteLine();
            //Preiau continutul tag-ului de text
            XmlNodeList xmList = xmldoc.GetElementsByTagName("text");
            Console.WriteLine("Continutul tag-ului de text este: ");
            Console.WriteLine();
            Console.WriteLine(xmList[0].InnerText.ToString());


            //separ dupa spatiu 
            title_words = xnList[0].InnerText.ToString().Split(' ');
            text_words = xmList[0].InnerText.ToString().Split(' ');

            //TO LOWER CASE
            foreach (string word in title_words)
            {
                aux.Add(word.ToLower());
            }
            title_words = aux.ToArray();

            aux.Clear();

            foreach (string word in text_words)
            {
                aux.Add(word.ToLower());
            }
            text_words = aux.ToArray();
            aux.Clear();

        }

        //**************************************************************************************************************************************************
       //This function gets rid of numbers numbers
        //***************************************************************************************************************************************************
        List<string> GetRidOfNumbers( List<string> aux)
        {
            List<string> temp = new List<string>();
            
            for (i = 0; i < aux.Count(); i++)
            {
                {
                    //verific daca cuvantul este un numar 
                    if (!Regex.IsMatch(aux[i], @"\d"))
                    {
                        temp.Add(aux[i]);
                    }
                }
            }
            return temp;
        }
        //**************************************************************************************************************************************************
        //This function gets rid of posesive
        //***************************************************************************************************************************************************
        List<string> GetRidOfPossessiv(List<string> aux)
        {
            List<string> temp = new List<string>();

            for (i = 0; i < aux.Count(); i++)
            {
                {
                    
                    //verific daca cuvantul este un numar 
                    if (aux[i].Contains("'s"))
                    {
                        string[] character = aux[i].Split('\'');
                        temp.Add(character[0]);
                    }
                    else
                    {
                        temp.Add(aux[i]);
                    }
                }
            }
            return temp;
        }
        //**************************************************************************************************************************************************
        //This function gets rid of stopWords
        //***************************************************************************************************************************************************
        List<string> GetRidOfStopWords(List <string> aux)
        {
            string docPath = Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);
            List<string> temp = new List<string>();
            List<string> Stop_words = new List<string>();
            StreamReader inputFile = new StreamReader(Path.Combine(docPath, "Stop_words.txt"));

            string line;
            // Read and display lines from the file until the end of
            // the file is reached.
            int plm = 0;
            while ((line = inputFile.ReadLine()) != null)
            {
                Stop_words.Add(line);
            }
            int ct;
            foreach (string word in aux)
            {
                ct = 0;
                foreach (string word2 in Stop_words)
                {

                    //verific daca cuvantul este un stop_word 
                    if (!word.Equals(word2))
                    {
                        ct++;
                    }
                }
                if (ct == Stop_words.Count)
                {
                    temp.Add(word);
                }
            }
            return temp;
        }
        //**************************************************************************************************************************************************
        //This function reads a every parsed by space word from title  tag and verifies if there is any need to parse again
        //Also counts the number of words in list 
        //***************************************************************************************************************************************************

        public void Title_Parser()
        {
           
            foreach (string word  in title_words)
            {

                if (word.Contains(" ") || word.Contains(".") || word.Contains(",") || word.Contains("\"") || word.Contains("") || word.Contains(":") || word.Contains("(") || word.Contains(")") || word.Contains("$") || word.Contains("/t") || word.Contains("&") || word.Contains("*"))
                {
                    //verific unde se afla punctul la nivel de cuvant 
                    //daca este la final inseamna ca este abreviere ,daca era sfarsit de propozitie inseamna ca avea spatiu dupa 

                    string[] new_word = word.Split(' ', '.', ',', '\"', ':', '/', '(', ')', '$', '-','\t','&','*');
                    for (int i = 0; i < new_word.Count(); i++)
                    {
                        if (new_word[i] != "")
                        {
                            aux.Add(new_word[i]);
                        }
                        
                    }
                }
                else
                {
                    aux.Add(word);
                }
            }
           aux= GetRidOfNumbers(aux);
           aux = GetRidOfStopWords(aux);
           aux = GetRidOfPossessiv(aux);
           aux = GetRidOfRoot(aux);


            //salvez continutul listei auxiliare in lista mea 
            title_words = aux.ToArray();
            //System.Console.WriteLine("Contor cuvinte in titlu  " + title_words.Length.ToString());

            //golesc lista aux
            aux.Clear();

        }

        //**************************************************************************************************************************************************
        //This function reads a every parsed by space word from text tag and verifies if there is any need to parse again
        //Also counts the number of words in list 
        //***************************************************************************************************************************************************
        public void TextParser()
        {
           

            //verific daca cuvantul contine punct incerc sa separ dupa el 
            foreach (string word in text_words)
            {

                if (word.Contains(" ") || word.Contains(".") || word.Contains(",") || word.Contains("\"") || word.Contains("") || word.Contains(":") || word.Contains("(") || word.Contains(")") || word.Contains("$") || word.Contains("/t") || word.Contains("&") || word.Contains("*"))
                {

                    string[] new_word = word.Split(' ', '.', ',', '\"', ':', '/', '(', ')', '$', '-', '\t', '&', '*');
                    for (i = 0; i < new_word.Count(); i++)
                    {
                        if (new_word[i] != "")
                        {
                            aux.Add(new_word[i]);
                        }
                       
                    }
                }
                else
                {
                    
                        aux.Add(word);
                }
            }
            aux=GetRidOfNumbers( aux);
            aux = GetRidOfStopWords(aux);
            aux = GetRidOfPossessiv(aux);
            aux = GetRidOfRoot(aux);

            text_words = aux.ToArray();

           
            //System.Console.WriteLine("Contor cuvinte in text  " + text_words.Length.ToString());
            aux.Clear();

        }


        //**************************************************************************************************************************************************
        //This function 
        //***************************************************************************************************************************************************
        public void PopulateDictionaryText()
        {
            bool[] vec = new bool [text_words.Count()];
            for (int i = 0; i < text_words.Count();)
            {
                if (vec[i] != true)
                {

                    for (int j = i; j < text_words.Count(); j++)
                    {
                        if (text_words[i].Equals(text_words[j]))
                        {
                            ct++;
                            vec[j] = true;
                        }
                    }

                    if (!GlobalWords.ContainsKey(text_words[i]))
                    {
                        GlobalWords.Add(text_words[i], ct);

                    }
                    else
                    {
                        GlobalWords[text_words[i]] = GlobalWords[text_words[i]] + ct;
                        
                    }
                    if (!FileTextWords.ContainsKey(text_words[i]))
                    {
                        FileTextWords.Add(text_words[i], ct);

                    }

                    else
                    {
                      
                        FileTextWords[text_words[i]] =FileTextWords[text_words[i]] + ct;
                    }
                    i++;
                    
                }
                else
                {
                    i++;
                }
                ct = 0;
            }

        }
        //**************************************************************************************************************************************************
        //This function  display dictionary data type content 
        //***************************************************************************************************************************************************

       
        public void PrinDictionary()
        {
            Console.WriteLine("Afisare dictionar");
            Console.WriteLine();
            foreach (KeyValuePair<string, int> kvp in GlobalWords)
            {
                Console.WriteLine(kvp.Key + "  " + kvp.Value);
                Console.WriteLine();
            }

        }

        //**************************************************************************************************************************************************
        //This function  display  Title  tag words
        //***************************************************************************************************************************************************
        public void Print_Title_words()
        {
            Console.WriteLine("------------------------------------------------------------------");
            Console.WriteLine("Parsare pentru titlu");
            Console.WriteLine();
            foreach (string word in title_words)
            {

                System.Console.WriteLine($"{word}");
            }
        }
        //**************************************************************************************************************************************************
        //This function  display  Text tag  words
        //***************************************************************************************************************************************************
       public void Print_Text_words()
        {
            Console.WriteLine("------------------------------------------------------------------");
            Console.WriteLine("Parsare pentru text");
            Console.WriteLine();
            foreach (string word in text_words)
            {
                System.Console.WriteLine($"{word}");
            }
        }

    //**************************************************************************************************************************************************
    //This function poplates dictionary with words from titile that were not found in text tag 
    //CUVANT-KEY     NR_APARITII-VALUE
    //verific daca cuvantul se afla in dictionarul meu ,daca nu il adaug si incrementez contorul sau salvat in valoare
    //***************************************************************************************************************************************************


    public void PopulateDictionaryTitle()
        {
            bool[] vec = new bool[title_words.Count()];
            for (int i = 0; i < title_words.Count();)
            {
                if (vec[i] != true)
                {

                    for (int j = i; j < title_words.Count(); j++)
                    {
                        if (title_words[i].Equals(title_words[j]))
                        {
                            ct++;
                            vec[j] = true;
                        }
                    }

                    if (!GlobalWords.ContainsKey(title_words[i]))
                    {
                        GlobalWords.Add(title_words[i], ct);

                    }
                    else
                    {
                        GlobalWords[title_words[i]] = GlobalWords[title_words[i]] + ct;

                    }
                    if (!FileTitleWords.ContainsKey(title_words[i]))
                    {
                        FileTitleWords.Add(title_words[i], ct);

                    }

                    
                   else
                    {
                        
                        FileTitleWords[title_words[i]] = FileTitleWords[title_words[i]] + ct;
                    }
                    i++;

                }
                else
                {
                    i++;
                }
                ct = 0;
            }


        }
        //**************************************************************************************************************************************************
        //This function populates dictionary with words from title and text
        //CUVANT-KEY     NR_APARITII-VALUE
        //***************************************************************************************************************************************************


        public void PopulateDictionaryDocument()
        {
            FileWords = FileTextWords;
            int count = 0;
           
            foreach (KeyValuePair<string, int> title_words in FileTitleWords)
            {
                
                foreach (KeyValuePair<string, int> kvp in FileTextWords.ToList())
                {
               
                   
                    if (title_words.Key.Equals(kvp.Key))
                    {
                        FileWords[title_words.Key] = FileWords[title_words.Key] + title_words.Value;
                        count = 0;
                        
                        
                    }
                    else
                    {
                        count++;
                    }
                       
                    
                }
                if (count == FileTextWords.Count())
                {

                    FileWords.Add(title_words.Key, title_words.Value);
                    count = 0;
                }

            }
        }

        //**************************************************************************************************************************************************
        //This function get every file from directory specified in the path,extract every text and title tag 
        //and parse it's content on the screen by space spliter
        //***************************************************************************************************************************************************

        public void SimpleParser_AllFiles()
        {

            //Citirea din mai multe fisiere a tag - ului de title si text si dupa separa toate cuvintele cate unul pe rand


           // string FilePath = @"E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_34\";
            string FilePath = @"E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_7083\";
            //E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_7083
            int i = 0;
            foreach (string file in Directory.EnumerateFiles(FilePath, "*.xml"))
            {
                i++;
                Console.WriteLine("-----------------------------------------------------------------------");
                Console.WriteLine("Numarul fisierului " + i);
                Console.WriteLine("-----------------------------------------------------------------------");
                XmlDocument xmldoc = new XmlDocument();
                xmldoc.LoadXml(File.ReadAllText(file));
                XmlNodeList xnList = xmldoc.GetElementsByTagName("title");
                XmlNodeList xmList = xmldoc.GetElementsByTagName("text");

                 title_words = xnList[0].InnerText.ToString().Split(' ');
                 text_words = xmList[0].InnerText.ToString().Split(' ');




                Console.WriteLine("Continutul tag-ului de title este :");
                Console.WriteLine("-----------------------------------------------------------------------");
                Console.WriteLine(xnList[0].InnerText.ToString());
                Console.WriteLine();


                foreach (var word in title_words)
                {
                    System.Console.WriteLine($"<{word}>");
                }

                Console.WriteLine("Continutul tag-ului de text este: ");
                Console.WriteLine("-----------------------------------------------------------------------");
                Console.WriteLine(xmList[0].InnerText.ToString());
                Console.WriteLine();

                foreach (var word in text_words)
                {
                    System.Console.WriteLine($"<{word}>");
                }

                //TO LOWER CASE
                foreach (string word in title_words)
                {
                    aux.Add(word.ToLower());
                }
                title_words = aux.ToArray();

                aux.Clear();

                foreach (string word in text_words)
                {
                    aux.Add(word.ToLower());
                }
                text_words = aux.ToArray();
                aux.Clear();

            }
        }

        //**************************************************************************************************************************************************
        //This function write to an file the content of LocalDictionary for each File
        //***************************************************************************************************************************************************

        void WriteToFile( Dictionary<string, int> fileWords,string fileName)
        {
            // Set a variable to the Documents path.
            string docPath =
              Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);

            // Write the string array to a new file named "WriteLines.txt".
            using (StreamWriter outputFile = new StreamWriter(Path.Combine(docPath, fileName)))
            {
                

                foreach (KeyValuePair<string, int> kvp in fileWords)
                {
                    outputFile.WriteLine(kvp.Key + "  " + kvp.Value);

                }

            }
        }

        //**************************************************************************************************************************************************
        //This function write to an file the content of LocalVectors of words for each File and GlobalArray
        //***************************************************************************************************************************************************

        void WriteToFileVector(string[][] fileWords, string fileName)
        {
            // Set a variable to the Documents path.
            string docPath =
              Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments);

            // Write the string array to a new file named "WriteLines.txt".
            using (StreamWriter outputFile = new StreamWriter(Path.Combine(docPath, fileName)))
            {
                for (int i = 0; i < GlobalArray.Length; i++)
                {

                    outputFile.Write(GlobalArray[i] + " ");


                }
                outputFile.WriteLine();

                for (int i = 0; i < fileWords.Length; i++)
                {
                    for (int j = 0; j < GlobalWords.Count(); j++)
                    {
                        outputFile.Write(fileWords[i][j] + " ");
                    }
                    outputFile.WriteLine();
                }


            }
        }
       


        //**************************************************************************************************************************************************
        //This function get every file from directory specified in the path,extract every text and title tag 
        //and parse it's content ,the parced content (word -frequency)should be stored in a output file 
        //***************************************************************************************************************************************************

        public void Parse_AllFiles()
        {

            //Citirea din mai multe fisiere a tag - ului de title si text si dupa separa toate cuvintele cate unul pe rand


           string FilePath = @"E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_34\";
           // string FilePath = @"E:\Facultate_an3\Sem2\RecunoastereaImaginilor\Laborator\Reuters_7083\";
            int number_of_files = 0;
           // Count_for_Files = Directory.GetFiles().Length
            foreach (string file in Directory.EnumerateFiles(FilePath, "*.xml"))
            {
                number_of_files++;//number of file
                
            
                XmlDocument xmldoc = new XmlDocument();
                xmldoc.LoadXml(File.ReadAllText(file));
                XmlNodeList xnList = xmldoc.GetElementsByTagName("title");
                XmlNodeList xmList = xmldoc.GetElementsByTagName("text");

                title_words = xnList[0].InnerText.ToString().Split(' ');
                text_words = xmList[0].InnerText.ToString().Split(' ');


                //foreach (var word in title_words)
                //{
                //    System.Console.WriteLine($"<{word}>");
                //}

                //foreach (var word in text_words)
                //{
                //    System.Console.WriteLine($"<{word}>");
                //}

                //TO LOWER CASE
                foreach (string word in title_words)
                {
                    aux.Add(word.ToLower());
                }
                title_words = aux.ToArray();

                aux.Clear();

                foreach (string word in text_words)
                {
                    aux.Add(word.ToLower());
                }
                text_words = aux.ToArray();
                aux.Clear();

                Title_Parser();
                TextParser();
               //Print_Title_words();
               //Print_Text_words();
                PopulateDictionaryTitle();
                PopulateDictionaryText();
              
                WriteToFile(FileTitleWords,"OutputFileTitle"+ number_of_files + ".txt");
                WriteToFile(FileTextWords, "OutputFileText" + number_of_files + ".txt");
                  PopulateDictionaryDocument();
                WriteToFile(FileWords, "OutputFileDocument" + number_of_files + ".txt");

                FileTitleWords.Clear();
                FileTextWords.Clear();
                FileWords.Clear();

            }
            Count_for_Files=number_of_files;
            WriteToFile(GlobalWords, "OutputFile.txt");
        }
        
        static void Main(string[] args)
        {


            SearchEngine MySearchEngine = new SearchEngine();
            // MySearchEngine.SingleFileReader();
             //MySearchEngine.SimpleParser_AllFiles();
            //MySearchEngine.Title_Parser();
            //MySearchEngine.TextParser();
            //MySearchEngine.Print_Title_words();
            //MySearchEngine.Print_Text_words();

            //MySearchEngine.PopulateDictionaryTitle();
            //MySearchEngine.WriteToFile(MySearchEngine.GlobalWords, "TitluOutput.txt");
            //MySearchEngine.PopulateDictionaryText();
            //MySearchEngine.WriteToFile(MySearchEngine.GlobalWords, "TextOutput.txt");
            //MySearchEngine.PrinDictionary();
            MySearchEngine.Parse_AllFiles();
            MySearchEngine.GlobalArray= MySearchEngine.CreateGlobalArray(MySearchEngine.GlobalWords);
            string[][] DocumentVectors=new string[MySearchEngine.Count_for_Files][];
            for (int i=0;i<MySearchEngine.Count_for_Files;i++)
            {
                DocumentVectors[i] = new string[MySearchEngine.GlobalWords.Count()];
                MySearchEngine.test = MySearchEngine.CheckDocument(MySearchEngine.GlobalWords, i);
                for (int j = 0; j < MySearchEngine.GlobalWords.Count(); j++)
                {


                    DocumentVectors[i][j] = MySearchEngine.test[j];
                }
            }
          
            MySearchEngine.WriteToFileVector(DocumentVectors,"vectori.txt");
          





        }
    }
}


