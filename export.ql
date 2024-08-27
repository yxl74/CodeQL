import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android

class PotentiallyExposedComponent extends AndroidComponent {
  PotentiallyExposedComponent() {
    // Components explicitly marked as exported in the manifest
    isExported()
    or
    // Components with intent filters (implicitly exported unless android:exported="false")
    hasIntentFilter() and not isExplicitlyUnexported()
    or
    // Any dynamically registered component
    exists(MethodAccess ma |
      ma.getMethod().hasName([
        "registerReceiver", 
        "registerActivity", 
        "registerService", 
        "registerContentProvider",
        "startService",
        "bindService",
        "startActivity",
        "startActivityForResult"
      ]) and
      (
        ma.getAnArgument().getType() = this.getClass()
        or
        ma.getAnArgument().(VarAccess).getVariable().getType() = this.getClass()
      )
    )
    or
    // Content providers are considered exposed by default in Android < 4.2
    this instanceof AndroidContentProvider
    or
    // Any component that's the target of an Intent
    exists(ClassInstanceExpr newIntent |
      newIntent.getType() instanceof TypeIntent and
      newIntent.getAnArgument().getType() = this.getClass()
    )
    or
    // Any component mentioned in a PendingIntent
    exists(MethodAccess ma |
      ma.getMethod().getDeclaringType() instanceof TypePendingIntent and
      ma.getAnArgument().getType() = this.getClass()
    )
  }

  predicate isExplicitlyUnexported() {
    exists(AndroidManifestXmlElement elem |
      elem = this.getAndroidManifestXmlElement() and
      elem.getAttribute("android:exported") = "false"
    )
  }
}

from PotentiallyExposedComponent component
select component, 
  "This component is potentially exposed to external interactions. " +
  "Reason: " + 
  (if component.isExported()
    then "Explicitly exported in the manifest. "
   else "") +
  (if component.hasIntentFilter() and not component.isExplicitlyUnexported()
    then "Has an intent filter and not explicitly unexported. "
   else "") +
  (if exists(MethodAccess ma |
      ma.getMethod().hasName([
        "registerReceiver", 
        "registerActivity", 
        "registerService", 
        "registerContentProvider",
        "startService",
        "bindService",
        "startActivity",
        "startActivityForResult"
      ]) and
      (
        ma.getAnArgument().getType() = component.getClass()
        or
        ma.getAnArgument().(VarAccess).getVariable().getType() = component.getClass()
      )
    ) then "Potentially dynamically registered or started. "
   else "") +
  (if component instanceof AndroidContentProvider
    then "Is a ContentProvider (potentially exposed by default in Android < 4.2). "
   else "") +
  (if exists(ClassInstanceExpr newIntent |
      newIntent.getType() instanceof TypeIntent and
      newIntent.getAnArgument().getType() = component.getClass()
    ) then "Used as an Intent target. "
   else "") +
  (if exists(MethodAccess ma |
      ma.getMethod().getDeclaringType() instanceof TypePendingIntent and
      ma.getAnArgument().getType() = component.getClass()
    ) then "Used in a PendingIntent. "
   else "") +
  "Verify if this exposure is intentional and properly secured."