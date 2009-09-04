using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Applications.Games.Escape
{
    public class Player
    {
        #region Instantiate player attributes.

        // Initialize Player attributes.
        public int Lives = 10, Score = 0, Level = 0, Movement = 0, X = 0, Y = 0, Z = 0, Variance = 0;
        public string Move = "None";
        public bool Resting = false, Playing = true;

        #endregion

        #region Define constructors for player class.

        public Player()
        {

        }

        #endregion

        #region Define update function for player attributes.

        public void updateLivesOnDeath()
        {
            this.Lives--;
        }

        public void updateLivesOnBonus()
        {
            this.Lives++;
        }

        public void updateScore()
        {
            this.Score += 10 + this.Level;
        }

        public void updateScoreForRiddle()
        {
            this.Score += 100;
        }

        public void updateLevel()
        {
            this.Level++;
        }

        #endregion

        #region Helper Functions.

        public int getAdvanceCount()
        {
            // Return the correct amount of moves needed to advance.
            return this.Level * 2 + 2;
        }

        public void RelayInfo()
        {
            Sounds Sound = new Sounds();
            Sound.YouHave.Play();
            Sound.PlayNumberSound(this.Lives);
            Sound.LivesLeft.Play();
            Sound.YouHave.Play();
            Sound.PlayNumberSound(this.Score);
            Sound.Points.Play();
        }

        #endregion
    }
}
