using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Threading;
using Wockets.Utils;
using Wockets.Applications.Games.Escape;
using System.IO;

namespace Wockets.Applications.Games.Escape
{
    public class Escape
    {
        public string Move;
        public static Player User = new Player();
        public string _Move
        {
            get { return this.Move; }
            set { User.Move = value; }
        }

        public bool isGaming = true;

        public void PlayExergame()
        {
            #region Gaming

            if (isGaming)
            {
                #region Variables.

                Actions Action = new Actions();
                Sounds Sound = new Sounds();

                int WrongCount = 0, Count = 0, RandomNumber = 0;
                bool GameOver = false;
                string Command = "", Move = "";
                Random random = new Random();

                #endregion

                Sound.GameStarting.Play();
                User.Playing = true;
                User.Lives = 10;
                GameOver = false;

                while (User.Playing)
                {
                    #region Game Play.

                    User.RelayInfo();

                    for (int i = 0; i < 3; i++)
                        Sound.PlayNumberSound(3 - i);

                    WrongCount = 0;
                    Count = 0;

                    while (Count < User.getAdvanceCount())
                    {
                        #region Level Play.

                        RandomNumber = random.Next(Action.PossibleCommands.Count);
                        Command = (string)Action.PossibleCommands[RandomNumber];
                        Move = Action.PossibleMoves[Command];
                        Action.PossibleSounds[Command].Play();

                        Thread.Sleep(3000);
                        if (User.Level < 5)
                            Thread.Sleep(2000);
                        else if (User.Level < 10)
                            Thread.Sleep(1500);
                        else if (User.Level < 15)
                            Thread.Sleep(1000);
                        else if (User.Level < 20)
                            Thread.Sleep(500);

                        RandomNumber = random.Next(100);
                        if (RandomNumber > 95)
                            Sound.YouWereAttacked.Play();
                        else if (User.Move.ToUpper() == Move.ToUpper())
                        {
                            Count++;
                            User.updateScore();
                            WrongCount = 0;
                            Sound.Ding.Play();
                        }
                        else if (User.Move == null)
                        {
                            if (User.Level != 1)
                                User.updateLivesOnDeath();
                            WrongCount++;
                            Sound.Buzz.Play();
                        }
                        else
                        {
                            if (User.Level != 1)
                                User.updateLivesOnDeath();
                            WrongCount++;
                            Sound.Buzz.Play();
                            Sound.WrongMove.Play();
                        }

                        if (User.Lives == 0)
                        {
                            GameOver = true;
                            break;
                        }
                        else if (WrongCount >= 3 && User.Level < 2)
                        {
                            Sound.Help.Play();
                            WrongCount = 0;
                        }

                        Thread.Sleep(500);
                        #endregion
                    }

                    #region End of level play.

                    if (GameOver)
                    {
                        Sound.GameOver.Play();
                        User.Playing = false;
                        break;

                        int HighScore = 0;
                        string Score = "";

                        TextWriter tw = new StreamWriter("HighScore.txt", true);
                        tw.Close();
                        TextReader tr = new StreamReader("HighScore.txt");
                        Score = tr.ReadLine();
                        if (Score != null)
                            HighScore = int.Parse(Score);
                        tr.Close();
                        if (User.Score > HighScore)
                        {
                            Sound.NewHighScore.Play();
                            TextWriter tw2 = new StreamWriter("HighScore.txt", true);
                            tw2.WriteLine(User.Score.ToString());
                            tw2.Close();
                        }
                    }
                    else
                    {
                        // Play game during rest period.
                        PlayRiddleGame(User, Action);
                        User.Resting = false;

                        Thread.Sleep(1000);

                        // Add move or word for reaching new level.
                        if (User.Level % 2 == 1)
                            Action.addMove();
                        else
                            Action.addCommand();

                        // Update user's level.
                        User.updateLevel();
                    }

                    #endregion

                    #endregion
                }
            }

            #endregion Gaming
        }

        private void PlayRiddleGame(Player User, Actions Action)
        {
            User.Resting = true;

            Random random = new Random();
            int RandomNumber = 0, Attempts = 0;
            string Command = "", Command2 = "", Move = "", Move2 = "";
            bool OneClear = false, TwoClear = false;
            ArrayList Letters = new ArrayList();
            Sounds Sound = new Sounds();

            RandomNumber = random.Next(Action.PossibleCommands.Count);
            Command = (string)Action.PossibleCommands[RandomNumber];
            Move = Action.PossibleMoves[Command];

            RandomNumber = random.Next(Action.PossibleCommands.Count);
            Command2 = (string)Action.PossibleCommands[RandomNumber];
            Move2 = Action.PossibleMoves[Command2];

            foreach (char Letter in Command)
                Letters.Add(Letter);

            if (User.Level < 10)
                Letters = Mix(Letters);
            else
            {
                foreach (char Letter in Command2)
                    Letters.Add(Letter);
                Letters = Mix(Letters);
            }

            Sound.Unscramble.Play();

            while ((!OneClear || !TwoClear) && Attempts < 7)
            {
                foreach (char Letter in Letters)
                    Sound.LetterToSound[Letter.ToString().ToUpper()].Play();

                Thread.Sleep(5000);

                Attempts++;

                if (User.Move.ToUpper() == Move.ToUpper() && !OneClear)
                {
                    Sound.Ding.Play();

                    User.updateScoreForRiddle();
                    OneClear = true;
                }

                if (User.Level < 10)
                    TwoClear = true;
                else if (User.Move.ToUpper() == Move2.ToUpper() && !TwoClear)
                {
                    Sound.Ding.Play();

                    User.updateScoreForRiddle();
                    TwoClear = true;
                }
            }
        }

        private ArrayList Mix(ArrayList Letters)
        {
            int Size = Letters.Count, RandomNumber = 0;
            Random random = new Random();
            ArrayList NewLetters = new ArrayList();

            for (int i = 0; i < Size; i++)
            {
                RandomNumber = random.Next(Letters.Count);
                NewLetters.Add(Letters[RandomNumber]);
                Letters.Remove(Letters[RandomNumber]);
            }

            return NewLetters;
        }

    }
}
