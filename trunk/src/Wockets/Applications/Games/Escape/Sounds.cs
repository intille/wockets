using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Windows.Forms;

namespace Wockets.Applications.Games.Escape
{
    public class Sounds
    {
        static string NEEDED_FILES_PATH;

        public Sounds(string Path)
        {
            NEEDED_FILES_PATH = Path;
        }

        // Instantiate Sounds
        //static string link = "Program Files\\Game v1\\";
        static string link = "\\Program Files\\wockets\\NeededFiles\\sounds\\GameSounds\\";
        static string link2 = NEEDED_FILES_PATH + "sounds\\GameSounds\\Actions\\";
        static string link3 = NEEDED_FILES_PATH + "sounds\\GameSounds\\Commands\\";
        static string link4 = NEEDED_FILES_PATH + "sounds\\GameSounds\\Connectors\\";
        static string link5 = NEEDED_FILES_PATH + "sounds\\GameSounds\\Letters\\";
        static string link6 = NEEDED_FILES_PATH + "sounds\\GameSounds\\Numbers\\";

        #region Actions.
        public Audio JumpingJacks = new Audio(link2 + "JumpingJacks.wav");
        public Audio Shake = new Audio(link2 + "Shake.wav");
        public Audio Jump = new Audio(link2 + "Jump.wav");
        public Audio Freeze = new Audio(link2 + "Freeze.wav");
        public Audio Liedown = new Audio(link2 + "Liedown.wav");
        public Audio Run = new Audio(link2 + "Run.wav");
        public Audio Stand = new Audio(link2 + "Stand.wav");
        public Audio Sit = new Audio(link2 + "Sit.wav");
        public Audio Walk = new Audio(link2 + "Walk.wav");
        public Audio Situps = new Audio(link2 + "Situps.wav");
        public Audio Pushups = new Audio(link2 + "Pushups.wav");
        public Audio[] SoundList;
        #endregion

        #region Connectors.

        public Audio AlsoMeans = new Audio(link4 + "AlsoMeans.wav");
        public Audio NowMeans = new Audio(link4 + "NowMeans.wav");
        public Audio Means = new Audio(link4 + "Means.wav");
        public Audio Unscramble = new Audio(link4 + "Unscramble");
        public Audio GameStarting = new Audio(link4 + "GameStarting.wav");
        public Audio GameOver = new Audio(link4 + "GameOver.wav");
        public Audio LivesLeft = new Audio(link4 + "LivesLeft.wav");
        public Audio YouHave = new Audio(link4 + "YouHave.wav");
        public Audio Points = new Audio(link4 + "Points.wav");
        public Audio You = new Audio(link4 + "You.wav");
        public Audio YouWereAttacked = new Audio(link4 + "YouWereAttacked.wav");
        public Audio YouMissed = new Audio(link4 + "YouMissed.wav");
        public Audio WrongMove = new Audio(link4 + "WrongMove.wav");
        public Audio Tripped = new Audio(link4 + "Tripped.wav");
        public Audio TooSlow = new Audio(link4 + "TooSlow.wav");
        public Audio NewHighScore = new Audio(link4 + "NewHighScore.wav");
        public Audio Help = new Audio(link4 + "Help.wav");
        public Audio Ding = new Audio(link4 + "Ding.wav");
        public Audio Buzz = new Audio(link4 + "Buzz.wav");
        #endregion

        #region Numbers.
        public static Audio Zero = new Audio(link6 + "Zero.wav");
        public static Audio One = new Audio(link6 + "One.wav");
        public static Audio Two = new Audio(link6 + "Two.wav");
        public static Audio Three = new Audio(link6 + "Three.wav");
        public static Audio Four = new Audio(link6 + "Four.wav");
        public static Audio Five = new Audio(link6 + "Five.wav");
        public static Audio Six = new Audio(link6 + "Six.wav");
        public static Audio Seven = new Audio(link6 + "Seven.wav");
        public static Audio Eight = new Audio(link6 + "Eight.wav");
        public static Audio Nine = new Audio(link6 + "Nine.wav");
        public static Audio Ten = new Audio(link6 + "Ten.wav");
        public static Audio Eleven = new Audio(link6 + "Eleven.wav");
        public static Audio Twelve = new Audio(link6 + "Twelve.wav");
        public static Audio Thirteen = new Audio(link6 + "Thirteen.wav");
        public static Audio Fourteen = new Audio(link6 + "Fourteen.wav");
        public static Audio Fifteen = new Audio(link6 + "Fifteen.wav");
        public static Audio Sixteen = new Audio(link6 + "Sixteen.wav");
        public static Audio Seventeen = new Audio(link6 + "Seventeen.wav");
        public static Audio Eighteen = new Audio(link6 + "Eighteen.wav");
        public static Audio Nineteen = new Audio(link6 + "Nineteen.wav");
        public static Audio Twenty = new Audio(link6 + "Twenty.wav");
        public static Audio Thirty = new Audio(link6 + "Thirty.wav");
        public static Audio Forty = new Audio(link6 + "Forty.wav");
        public static Audio Fifty = new Audio(link6 + "Fifty.wav");
        public static Audio Sixty = new Audio(link6 + "Sixty.wav");
        public static Audio Seventy = new Audio(link6 + "Seventy.wav");
        public static Audio Eighty = new Audio(link6 + "Eighty.wav");
        public static Audio Ninety = new Audio(link6 + "Ninety.wav");
        public static Audio Hundred = new Audio(link6 + "Hundred.wav");
        public static Audio Thousand = new Audio(link6 + "Thousand.wav");
        public Audio[] Numbers = new Audio[] { Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Eleven,
                                                                  Twelve, Thirteen, Fourteen, Fifteen, Sixteen, Seventeen, Eighteen, Nineteen };
        public Audio[] Tens = new Audio[] { Zero, Ten, Twenty, Thirty, Forty, Fifty, Sixty, Seventy, Eighty, Ninety };
        #endregion

        #region Letters.
        public Audio A = new Audio(link5 + "A.wav");
        public Audio B = new Audio(link5 + "B.wav");
        public Audio C = new Audio(link5 + "C.wav");
        public Audio D = new Audio(link5 + "D.wav");
        public Audio E = new Audio(link5 + "E.wav");
        public Audio F = new Audio(link5 + "F.wav");
        public Audio G = new Audio(link5 + "G.wav");
        public Audio H = new Audio(link5 + "H.wav");
        public Audio I = new Audio(link5 + "I.wav");
        public Audio J = new Audio(link5 + "J.wav");
        public Audio K = new Audio(link5 + "K.wav");
        public Audio L = new Audio(link5 + "L.wav");
        public Audio M = new Audio(link5 + "M.wav");
        public Audio N = new Audio(link5 + "N.wav");
        public Audio O = new Audio(link5 + "O.wav");
        public Audio P = new Audio(link5 + "P.wav");
        public Audio Q = new Audio(link5 + "Q.wav");
        public Audio R = new Audio(link5 + "R.wav");
        public Audio S = new Audio(link5 + "S.wav");
        public Audio T = new Audio(link5 + "T.wav");
        public Audio U = new Audio(link5 + "U.wav");
        public Audio V = new Audio(link5 + "V.wav");
        public Audio W = new Audio(link5 + "W.wav");
        public Audio X = new Audio(link5 + "X.wav");
        public Audio Y = new Audio(link5 + "Y.wav");
        public Audio Z = new Audio(link5 + "Z.wav");
        #endregion

        #region Word list sounds.
        public Audio Ancestor = new Audio(link3 + "Ancestor.wav");
        public Audio Angel = new Audio(link3 + "Angel.wav");
        public Audio Astronaut = new Audio(link3 + "Astronaut.wav");
        public Audio Banana = new Audio(link3 + "Banana.wav");
        public Audio Banjo = new Audio(link3 + "Banjo.wav");
        public Audio Blarney = new Audio(link3 + "Blarney.wav");
        public Audio Castle = new Audio(link3 + "Castle.wav");
        public Audio Cave = new Audio(link3 + "Cave.wav");
        public Audio Coconut = new Audio(link3 + "Coconut.wav");
        public Audio Danger = new Audio(link3 + "Danger.wav");
        public Audio Donkey = new Audio(link3 + "Donkey.wav");
        public Audio Doodle = new Audio(link3 + "Doodle.wav");
        public Audio Elderberry = new Audio(link3 + "Elderberry.wav");
        public Audio Emu = new Audio(link3 + "Emu.wav");
        public Audio Eyeball = new Audio(link3 + "Eyeball.wav");
        public Audio Finch = new Audio(link3 + "Finch.wav");
        public Audio Foghorn = new Audio(link3 + "Foghorn.wav");
        public Audio Fruit = new Audio(link3 + "Fruit.wav");
        public Audio Ghost = new Audio(link3 + "Ghost.wav");
        public Audio Goat = new Audio(link3 + "Goat.wav");
        public Audio Grail = new Audio(link3 + "Grail.wav");
        public Audio Hamster = new Audio(link3 + "Hamster.wav");
        public Audio Herring = new Audio(link3 + "Herring.wav");
        public Audio Horse = new Audio(link3 + "Horse.wav");
        public Audio Idea = new Audio(link3 + "Idea.wav");
        public Audio Inspector = new Audio(link3 + "Inspector.wav");
        public Audio Ivy = new Audio(link3 + "Ivy.wav");
        public Audio Jack = new Audio(link3 + "Jack.wav");
        public Audio Jello = new Audio(link3 + "Jello.wav");
        public Audio Jet = new Audio(link3 + "Jet.wav");
        public Audio Khaki = new Audio(link3 + "Khaki.wav");
        public Audio Knight = new Audio(link3 + "Knight.wav");
        public Audio Koala = new Audio(link3 + "Koala.wav");
        public Audio Lamp = new Audio(link3 + "Lamp.wav");
        public Audio Liger = new Audio(link3 + "Liger.wav");
        public Audio Llama = new Audio(link3 + "Llama.wav");
        public Audio Martian = new Audio(link3 + "Martian.wav");
        public Audio Mayor = new Audio(link3 + "Mayor.wav");
        public Audio Message = new Audio(link3 + "Message.wav");
        public Audio Nail = new Audio(link3 + "Nail.wav");
        public Audio Nat = new Audio(link3 + "Nat.wav");
        public Audio Newt = new Audio(link3 + "Newt.wav");
        public Audio Octopus = new Audio(link3 + "Octopus.wav");
        public Audio Olive = new Audio(link3 + "Olive.wav");
        public Audio Oval = new Audio(link3 + "Oval.wav");
        public Audio Parrot = new Audio(link3 + "Parrot.wav");
        public Audio Pickle = new Audio(link3 + "Pickle.wav");
        public Audio Python = new Audio(link3 + "Python.wav");
        public Audio Queen = new Audio(link3 + "Queen.wav");
        public Audio Quest = new Audio(link3 + "Quest.wav");
        public Audio Quiet = new Audio(link3 + "Quiet.wav");
        public Audio Racket = new Audio(link3 + "Racket.wav");
        public Audio Riot = new Audio(link3 + "Riot.wav");
        public Audio Robin = new Audio(link3 + "Robin.wav");
        public Audio Sausage = new Audio(link3 + "Sausage.wav");
        public Audio Shrubbery = new Audio(link3 + "Shrubbery.wav");
        public Audio Spam = new Audio(link3 + "Spam.wav");
        public Audio Talon = new Audio(link3 + "Talon.wav");
        public Audio Temple = new Audio(link3 + "Temple.wav");
        public Audio Trot = new Audio(link3 + "Trot.wav");
        public Audio Umbrella = new Audio(link3 + "Umbrella.wav");
        public Audio Unicorn = new Audio(link3 + "Unicorn.wav");
        public Audio Uranus = new Audio(link3 + "Uranus.wav");
        public Audio Van = new Audio(link3 + "Van.wav");
        public Audio Vendor = new Audio(link3 + "Vendor.wav");
        public Audio Vermin = new Audio(link3 + "Vermin.wav");
        public Audio Walrus = new Audio(link3 + "Walrus.wav");
        public Audio Whistle = new Audio(link3 + "Whistle.wav");
        public Audio Wrench = new Audio(link3 + "Wrench.wav");
        public Audio Xenon = new Audio(link3 + "Xenon.wav");
        public Audio Xerox = new Audio(link3 + "Xerox.wav");
        public Audio Xray = new Audio(link3 + "Xray.wav");
        public Audio Yams = new Audio(link3 + "Yams.wav");
        public Audio Yellow = new Audio(link3 + "Yellow.wav");
        public Audio Yogurt = new Audio(link3 + "Yogurt.wav");
        public Audio Zeal = new Audio(link3 + "Zeal.wav");
        public Audio Zing = new Audio(link3 + "Zing.wav");
        public Audio Zoo = new Audio(link3 + "Zoo.wav");


        #endregion

        #region Variables.
        public Dictionary<string, Audio> LetterToSound = new Dictionary<string, Audio>();
        #endregion

        #region Constructors.
        public Sounds()
        {
            // Add sounds to character list.
            this.LetterToSound.Add("A", A);
            this.LetterToSound.Add("B", B);
            this.LetterToSound.Add("C", C);
            this.LetterToSound.Add("D", D);
            this.LetterToSound.Add("E", E);
            this.LetterToSound.Add("F", F);
            this.LetterToSound.Add("G", G);
            this.LetterToSound.Add("H", H);
            this.LetterToSound.Add("I", I);
            this.LetterToSound.Add("J", J);
            this.LetterToSound.Add("K", K);
            this.LetterToSound.Add("L", L);
            this.LetterToSound.Add("M", M);
            this.LetterToSound.Add("N", N);
            this.LetterToSound.Add("O", O);
            this.LetterToSound.Add("P", P);
            this.LetterToSound.Add("Q", Q);
            this.LetterToSound.Add("R", R);
            this.LetterToSound.Add("S", S);
            this.LetterToSound.Add("T", T);
            this.LetterToSound.Add("U", U);
            this.LetterToSound.Add("V", V);
            this.LetterToSound.Add("W", W);
            this.LetterToSound.Add("X", X);
            this.LetterToSound.Add("Y", Y);
            this.LetterToSound.Add("Z", Z);

        }
        #endregion

        #region Helper functions.

        public void PlayNumberSound(int Number)
        {
            int i = Number % 1000;
            int j = Number / 1000;

            if (j != 0)
            {
                NumberSound(j / 100, (j / 10) % 10, j % 10);
                Thousand.Play();
            }
            NumberSound(i / 100, (i / 10) % 10, i % 10);
        }

        public void NumberSound(int hun, int ten, int one)
        {
            if (ten == 0 || ten == 1)
            {
                if (hun != 0)
                {
                    Numbers[hun].Play();
                    Hundred.Play();
                }
                Numbers[10 * ten + one].Play();
            }
            else if (one != 0 || ten != 0 || hun != 0)
            {
                if (hun != 0)
                {
                    Numbers[hun].Play();
                    Hundred.Play();
                }
                if (ten != 0)
                    Tens[ten].Play();
                if (one != 0)
                    Numbers[one].Play();
            }
            else
                Zero.Play();
        }

        #endregion
    }
}