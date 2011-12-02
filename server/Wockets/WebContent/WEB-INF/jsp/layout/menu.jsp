<%@ page language="java" contentType="text/html; charset=ISO-8859-1"
    pageEncoding="ISO-8859-1"%>
    <%@taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<html>
<body>

<div id="main-menu">
<h3>Wockets</h3>
<c:if test="${sessionScope.UserRole==null}">
<ul>
<li><a href="home.html">Home</a></li>
<li><a href="http://web.mit.edu/wockets/News.htm" target="_blank">What's new? </a></li>
<li><a href="http://web.mit.edu/wockets/Goals.htm" target="_blank">Goals</a></li>
<li><a href="http://web.mit.edu/wockets/FAQ.htm" target="_blank">FAQ</a></li>
<li><a href="http://web.mit.edu/wockets/Used.htm" target="_blank"> Who has used them?</a></li>
<li><a href="http://web.mit.edu/wockets/Team.htm" target="_blank">Team</a></li>
<li><a href="http://web.mit.edu/wockets/Acknowledgements.htm" target="_blank">Acknowledgements</a></li>
</ul>
<h3>Contribute</h3>
<ul>
<li><a href="http://web.mit.edu/wockets/MailingLists.htm" target="_blank">Join mailing list</a></li>
<li><a href="http://web.mit.edu/wockets/MailingListsArchives.htm" target="_blank">Read archives</a></li>
<li><a href="http://web.mit.edu/wockets/Design.htm" target="_blank">Critique designs</a></li>
<li><a href="http://wockets.wikispaces.com/" target="_blank">Add to Wiki</a></li>
<li><a href="http://web.mit.edu/wockets/Recruiting.htm" target="_blank">Help recruit</a></li>
<li><a href="http://web.mit.edu/wockets/Projects.htm" target="_blank">Do an independent project</a></li>
<li><a href="http://web.mit.edu/wockets/Consulting.htm" target="_blank">Consult</a></li>
<li><a href="http://web.mit.edu/wockets/Manufacturing.htm" target="_blank">Manufacture Wockets</a></li>
</ul>

<h3>Tell us:</h3>
<ul>
<li><a href="http://web.mit.edu/wockets/Uses.htm" target="_blank"> I want Wockets for...</a></li>
</ul>

<h3>Related efforts</h3>
<ul>
<li><a href="http://myexperience.sourceforge.net" target="_blank">MyExperience</a></li>
<li><a href="http://web.mit.edu/nesp" target="_blank">NESP</a></li>
</ul>
</c:if>


<c:if test="${sessionScope.UserRole=='A'}">
<!-- *********Admin links************* -->
<ul>
<li><a href="personalInfo.html">Personal Profile</a></li>
<li><a href ="userAccountDirec.html">Manage Users Account</a></li>
<li><a href ="phoneDirec.html">Manage Phones Directory</a></li>
<li><a href ="simDirec.html">Manage Simcards Directory</a></li>
<li><a href ="studyDirectory.html">Manage Study Directory</a></li>
<li><a href ="wocketsDirectory.html">Manage Wockets Directory</a></li>
<li><a href ="participantDirectory.html">Manage Participant Directory</a></li>
<li><a href ="newParticipant.html">Register New Participant</a></li>
</ul>
</c:if>

<c:if test="${sessionScope.UserRole=='R'}">
<!-- *********Reviewer links************* -->
<ul>
<li><a href="personalInfo.html">Personal Profile</a></li>
<li><a href="reviewerAssignedStudy.html">Assigned Study</a></li>
<li><a href="reviewerReviewPage.html">Review Participant</a></li>
<li><a href="reviewerDataCheck.html">Data Check</a></li>
</ul>
</c:if>


</div>

</body>
</html>


