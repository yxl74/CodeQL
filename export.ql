import android
import semmle.code.java.dataflow.FlowSources

class PotentiallyExposedComponent extends AndroidComponent {
  PotentiallyExposedComponent() {
    // All components are considered potentially exposed unless explicitly unexported
    not exists(AndroidManifest manifest, XMLElement elem |
      manifest.getApplication().getAChild*() = elem and
      elem.getName() = this.getKind() and
      elem.getAttribute("android:exported") = "false"
    )
    or
    // Any component with an intent filter
    exists(IntentFilter filter |
      filter.getComponent() = this
    )
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
        ma.getAnArgument().getType() = this.getType()
        or
        ma.getAnArgument().(VarAccess).getVariable().getType() = this.getType()
      )
    )
    or
    // Content providers are considered exposed by default in Android < 4.2
    this instanceof ContentProvider
    or
    // Any component that's the target of an Intent
    exists(ClassInstanceExpr newIntent |
      newIntent.getType() instanceof TypeIntent and
      newIntent.getAnArgument().getType() = this.getType()
    )
    or
    // Any component mentioned in a PendingIntent
    exists(MethodAccess ma |
      ma.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
      ma.getAnArgument().getType() = this.getType()
    )
  }
}

from PotentiallyExposedComponent component
select component, 
  "This component is potentially exposed to external interactions. " +
  "Reason: " + 
  (if not exists(AndroidManifest manifest, XMLElement elem |
      manifest.getApplication().getAChild*() = elem and
      elem.getName() = component.getKind() and
      elem.getAttribute("android:exported") = "false"
    ) then "Not explicitly unexported. "
   else "") +
  (if exists(IntentFilter filter | filter.getComponent() = component)
    then "Has an intent filter. "
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
        ma.getAnArgument().getType() = component.getType()
        or
        ma.getAnArgument().(VarAccess).getVariable().getType() = component.getType()
      )
    ) then "Potentially dynamically registered or started. "
   else "") +
  (if component instanceof ContentProvider
    then "Is a ContentProvider (potentially exposed by default in Android < 4.2). "
   else "") +
  (if exists(ClassInstanceExpr newIntent |
      newIntent.getType() instanceof TypeIntent and
      newIntent.getAnArgument().getType() = component.getType()
    ) then "Used as an Intent target. "
   else "") +
  (if exists(MethodAccess ma |
      ma.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
      ma.getAnArgument().getType() = component.getType()
    ) then "Used in a PendingIntent. "
   else "") +
  "Verify if this exposure is intentional and properly secured."