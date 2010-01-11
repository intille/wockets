using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace Wockets.Applications.Games.Escape
{
    public class Actions
    {
        #region Instantiate variables.

        // Instantiate sounds.
        static Sounds Sound = new Sounds();

        // To add an action: Add your word to the first list in red and the equivalent audio to the second list..
        public string[] ActionList = new string[] { "Freeze", "Shake", "Jump", "Walk", "Stand", "JumpingJacks", "Situps", "Pushups", "Run", "Liedown", "Sit" };
        public Audio[] ActionListSounds = new Audio[] { Sound.Freeze, Sound.Shake, Sound.Jump, Sound.Walk, Sound.Stand, Sound.JumpingJacks, Sound.Situps, Sound.Pushups, Sound.Run, Sound.Liedown, Sound.Sit };

        // To add a special commands: Add the word to the first list in red and the equivalent audio to the second list.
        public string[] WordList = new string[] { "Ancestor", "Angel", "Astronaut", "Banana", "Banjo", "Blarney", "Castle", "Cave", "Coconut", "Danger", "Donkey", "Doodle",
                                                  "Elderberry", "Emu", "Eyeball", "Finch", "Foghorn", "Fruit", "Ghost", "Goat", "Grail", "Hamster", "Herring", "Horse", "Idea",
                                                  "Inspector", "Ivy", "Jack", "Jet", "Jello", "Khaki", "Knight", "Koala", "Lamp", "Liger", "Llama", "Martian", "Mayor", "Message",
                                                  "Nail", "Newt", "Nat", "Octopus", "Olive", "Oval", "Parrot", "Pickle", "Python", "Queen", "Quest", "Quiet", "Racket", "Riot",
                                                  "Robin", "Sausage", "Shrubbery", "Spam", "Talon", "Temple", "Trot", "Umbrella", "Unicorn", "Uranus", "Van", "Vendor", "Vermin",
                                                  "Walrus", "Whistle", "Wrench", "Xenon", "Xerox", "Xray", "Yams", "Yellow", "Yogurt", "Zeal", "Zing", "Zoo" };
        public Audio[] WordListSounds = new Audio[] { Sound.Ancestor, Sound.Angel, Sound.Astronaut, Sound.Banana, Sound.Banjo, Sound.Blarney, Sound.Castle, Sound.Cave, Sound.Coconut, Sound.Danger, Sound.Donkey, Sound.Doodle,
                                                  Sound.Elderberry, Sound.Emu, Sound.Eyeball, Sound.Finch, Sound.Foghorn, Sound.Fruit, Sound.Ghost, Sound.Goat, Sound.Grail, Sound.Hamster, Sound.Herring, Sound.Horse, Sound.Idea,
                                                  Sound.Inspector, Sound.Ivy, Sound.Jack, Sound.Jet, Sound.Jello, Sound.Khaki, Sound.Knight, Sound.Koala, Sound.Lamp, Sound.Liger, Sound.Llama, Sound.Martian, Sound.Mayor, Sound.Message,
                                                  Sound.Nail, Sound.Newt, Sound.Nat, Sound.Octopus, Sound.Olive, Sound.Oval, Sound.Parrot, Sound.Pickle, Sound.Python, Sound.Queen, Sound.Quest, Sound.Quiet, Sound.Racket, Sound.Riot,
                                                  Sound.Robin, Sound.Sausage, Sound.Shrubbery, Sound.Spam, Sound.Talon, Sound.Temple, Sound.Trot, Sound.Umbrella, Sound.Unicorn, Sound.Uranus, Sound.Van, Sound.Vendor, Sound.Vermin,
                                                  Sound.Walrus, Sound.Whistle, Sound.Wrench, Sound.Xenon, Sound.Xerox, Sound.Xray, Sound.Yams, Sound.Yellow, Sound.Yogurt, Sound.Zeal, Sound.Zing, Sound.Zoo };

        // Initialize global variable.
        private int InitialMoveCount = 2, AddActionCount = 0;

        // Actions attributes.
        public ArrayList PossibleActions = new ArrayList();
        public ArrayList PossibleCommands = new ArrayList();
        public Dictionary<string, string> PossibleMoves = new Dictionary<string, string>();
        public Dictionary<string, Audio> PossibleSounds = new Dictionary<string, Audio>();
        public Dictionary<string, Audio> ActionsToSounds = new Dictionary<string, Audio>();
        public Dictionary<string, Audio> WordsToSounds = new Dictionary<string, Audio>();

        #endregion

        #region Define constructors for Actions class.

        public Actions()
        {
            // Add first level moves to action instance.
            for (int i = 0; i < this.InitialMoveCount; i++)
            {
                this.PossibleMoves.Add(this.ActionList[i], this.ActionList[i]);
                this.PossibleCommands.Add(this.ActionList[i]);
                this.PossibleActions.Add(this.ActionList[i]);
                this.PossibleSounds.Add(this.ActionList[i], this.ActionListSounds[i]);
            }

            // Create ActionsToSounds and WordsToSounds Dictionary.
            for (int i = 0; i < this.ActionList.Length; i++)
                this.ActionsToSounds.Add(this.ActionList[i], this.ActionListSounds[i]);
            for (int i = 0; i < this.WordList.Length; i++)
                this.WordsToSounds.Add(this.WordList[i], this.WordListSounds[i]);
        }

        #endregion

        #region Helper methods for Actions class.

        public void addMove()
        {
            // Initialize variables;
            int Index = 0;

            // If there are  moves left, add them to Possible Moves, Actions, and Commands, otherwise add new Command.
            if (this.AddActionCount < (this.ActionList.Length - this.InitialMoveCount))
            {
                Index = this.AddActionCount + this.InitialMoveCount;
                this.PossibleMoves.Add(this.ActionList[Index], this.ActionList[Index]);
                this.PossibleCommands.Add(this.ActionList[Index]);
                this.PossibleActions.Add(this.ActionList[Index]);
                this.PossibleSounds.Add(this.ActionList[Index], this.ActionListSounds[Index]);

                // Update AddActionCount because one of them has been used.
                this.AddActionCount++;
            }
            else
                this.addCommand();
        }

        public void addCommand()
        {
            // Instantiate variables.
            string Command = "", Action = "";
            int RandomNumber = 0;
            Boolean IsNew = false;
            Random random = new Random();

            // Get a SpecialWord and Action to be mapped.            
            RandomNumber = random.Next(this.WordList.Length);
            Command = this.WordList[RandomNumber];
            RandomNumber = random.Next(this.PossibleActions.Count);
            Action = (string)this.PossibleActions[RandomNumber];

            // Remove the Command-Action pair if it has been loaded to Moves already.
            if (this.PossibleMoves.ContainsKey(Command))
            {
                IsNew = false;
                this.PossibleMoves.Remove(Command);
            }

            // Add the new Command-Action pair.
            this.PossibleActions.Add(Action);
            this.PossibleCommands.Add(Command);
            this.PossibleMoves.Add(Command, Action);
            if (!this.PossibleSounds.ContainsKey(Command))
                this.PossibleSounds.Add(Command, this.WordsToSounds[Command]);

            this.WordsToSounds[Command].Play();
            if (!IsNew)
                Sound.AlsoMeans.Play();
            else
                Sound.NowMeans.Play();
            this.ActionsToSounds[Action].Play();
        }

        #endregion
    }
}
